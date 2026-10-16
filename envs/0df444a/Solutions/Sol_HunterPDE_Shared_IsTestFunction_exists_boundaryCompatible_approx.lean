-- Prove2me | solution 1 for HunterPDE.Shared.IsTestFunction.exists_boundaryCompatible_approx
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T08:13:30.051108+00:00
-- url     : https://prove2.me/submissions/ab8df46c-6314-4dd4-81ff-5bff83819dcf

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Filter HunterPDE.Shared
open scoped Topology ContDiff
set_option autoImplicit false

namespace BoundaryTestApprox

lemma list_single {n : ℕ} (i : Fin n) (l : List (Fin n)) (hl : l.Nodup) :
    l.flatMap (fun j => List.replicate ((Pi.single i 1 : Fin n → ℕ) j) j) =
      if i ∈ l then [i] else [] := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := (List.nodup_cons.mp hl).1
    have hh := ih (List.nodup_cons.mp hl).2
    by_cases h : a = i
    · subst a; simp [List.flatMap_cons, hh, ha]
    · simp [List.flatMap_cons, hh, h, Ne.symm h]

lemma multi_single {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) :
    multiDeriv φ (Pi.single i 1) = partialDeriv φ i := by
  unfold multiDeriv multiIndexList
  rw [list_single i (List.finRange n) (List.nodup_finRange n)]
  simp [iteratedPartial]

end BoundaryTestApprox

theorem solution (m : ℕ) (i : Fin (m + 1)) (ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hψ : HunterPDE.Shared.IsTestFunction Set.univ ψ)
    (hb : i = Fin.last m → ∀ x, x (Fin.last m) = 0 → ψ x = 0) :
    ∃ K : Set (EuclideanSpace ℝ (Fin (m + 1))), IsCompact K ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∃ φ : ℕ → EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
          (∀ n, HunterPDE.Shared.IsTestFunction (HunterPDE.Compactness.upperHalfSpace m) (φ n)) ∧
          (∀ n x, ‖φ n x‖ ≤ K.indicator (fun _ => C) x ∧
            ‖HunterPDE.Shared.multiDeriv (φ n) (Pi.single i 1) x‖ ≤
              K.indicator (fun _ => C) x) ∧
          (∀ x ∈ HunterPDE.Compactness.upperHalfSpace m,
            Tendsto (fun n => φ n x) atTop (𝓝 (ψ x)) ∧
            Tendsto (fun n => HunterPDE.Shared.multiDeriv (φ n) (Pi.single i 1) x)
              atTop (𝓝 (HunterPDE.Shared.multiDeriv ψ (Pi.single i 1) x))) := by
  classical
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let t : E →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last m)
  let q : ℝ → ℝ := Real.smoothTransition
  have hq : ContDiff ℝ ∞ q := Real.smoothTransition.contDiff
  have hqd : Differentiable ℝ q := hq.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
  have hz (s : ℝ) (hs : s < 0) : deriv q s = 0 := by
    have he : q =ᶠ[𝓝 s] (fun _ => 0) := by
      filter_upwards [gt_mem_nhds hs] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [he.deriv_eq]; simp
  have ho (s : ℝ) (hs : 1 < s) : deriv q s = 0 := by
    have he : q =ᶠ[𝓝 s] (fun _ => 1) := by
      filter_upwards [lt_mem_nhds hs] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [he.deriv_eq]; simp
  obtain ⟨D₀, hD₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 1) (hq.continuous_deriv (by simp)).continuousOn
  let D := max D₀ 0
  have hD : 0 ≤ D := le_max_right _ _
  have hdq (s : ℝ) : ‖deriv q s‖ ≤ D := by
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · exact (hD₀ s hs).trans (le_max_left _ _)
    · rcases not_and_or.mp hs with h | h
      · rw [hz s (lt_of_not_ge h), norm_zero]; exact hD
      · rw [ho s (lt_of_not_ge h), norm_zero]; exact hD
  obtain ⟨A₀, hA₀⟩ := hψ.2.1.exists_bound_of_continuous hψ.1.continuous
  obtain ⟨B₀, hB₀⟩ := (hψ.2.1.fderiv ℝ).exists_bound_of_continuous
    (hψ.1.continuous_fderiv (by simp))
  let A := max A₀ 0
  let B := max B₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hB : 0 ≤ B := le_max_right _ _
  have hval (x : E) : ‖ψ x‖ ≤ A := (hA₀ x).trans (le_max_left _ _)
  have hder (x : E) : ‖fderiv ℝ ψ x‖ ≤ B := (hB₀ x).trans (le_max_left _ _)
  have hpart (x : E) : ‖partialDeriv ψ i x‖ ≤ B := by
    simpa [partialDeriv] using
      ((fderiv ℝ ψ x).le_opNorm (EuclideanSpace.single i 1)).trans
        (mul_le_mul_of_nonneg_right (hder x) (norm_nonneg _))
  have hbval (hi : i = Fin.last m) (x : E) : ‖ψ x‖ ≤ B * |t x| := by
    let y := x - (t x) • EuclideanSpace.single (Fin.last m) (1 : ℝ)
    have hy : y (Fin.last m) = 0 := by
      change t y = 0
      simp only [y, map_sub, map_smul]
      have ht : t (EuclideanSpace.single (Fin.last m) 1) = 1 := by
        change (EuclideanSpace.single (Fin.last m) (1 : ℝ)) (Fin.last m) = 1
        simp
      rw [ht]; simp
    have hzero : ψ y = 0 := hb hi y hy
    have hnorm : ‖(EuclideanSpace.single (Fin.last m) (1 : ℝ) : E)‖ = 1 := by
      change ‖PiLp.single (β := fun _ : Fin (m + 1) => ℝ) 2 (Fin.last m) 1‖ = 1
      rw [PiLp.norm_single]; exact norm_one
    have hdist : ‖x - y‖ = |t x| := by
      simp only [y, sub_sub_cancel, norm_smul, Real.norm_eq_abs, hnorm, mul_one]
    have hm := Convex.norm_image_sub_le_of_norm_fderiv_le
      (s := Set.univ) (fun z _ => hψd z) (fun z _ => hder z)
      convex_univ (Set.mem_univ y) (Set.mem_univ x)
    simpa [hzero, hdist] using hm
  let a : ℕ → ℝ := fun n => (n : ℝ) + 1
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  let φ : ℕ → E → ℝ := fun n x => q (a n * t x - 1) * ψ x
  have hsmooth (n : ℕ) : ContDiff ℝ ∞ (φ n) :=
    (hq.comp ((contDiff_const.mul t.contDiff).sub contDiff_const)).mul hψ.1
  have hcompact (n : ℕ) : HasCompactSupport (φ n) := hψ.2.1.mul_left
  have hsupport (n : ℕ) : tsupport (φ n) ⊆ tsupport ψ := tsupport_mul_subset_right
  have hinterior (n : ℕ) : tsupport (φ n) ⊆ HunterPDE.Compactness.upperHalfSpace m := by
    have hclosed : IsClosed {x : E | 1 ≤ a n * t x} :=
      isClosed_le continuous_const (continuous_const.mul t.continuous)
    have hin : tsupport (φ n) ⊆ {x : E | 1 ≤ a n * t x} := by
      apply closure_minimal _ hclosed
      intro x hx
      change 1 ≤ a n * t x
      by_contra hh
      have hqzero : q (a n * t x - 1) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      exact hx (by simp [φ, hqzero])
    intro x hx
    have hh := hin hx
    change 1 ≤ a n * t x at hh
    change 0 < t x
    nlinarith [ha n]
  have hformula (n : ℕ) (x : E) : partialDeriv (φ n) i x =
      q (a n * t x - 1) * partialDeriv ψ i x +
        (deriv q (a n * t x - 1) * a n * t (EuclideanSpace.single i 1)) * ψ x := by
    have hlin : HasFDerivAt (fun y => a n * t y - 1) (a n • t) x :=
      (t.hasFDerivAt.const_mul (a n)).sub_const (1 : ℝ)
    have hchain := (hqd (a n * t x - 1)).hasDerivAt.comp_hasFDerivAt x hlin
    have hp := hchain.mul (hψd x).hasFDerivAt
    unfold partialDeriv
    change (fderiv ℝ ((q ∘ fun y => a n * t y - 1) * ψ) x)
      (EuclideanSpace.single i 1) = _
    rw [hp.fderiv]
    simp
    <;> ring
  let C := A + B + 2 * D * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hφval (n : ℕ) (x : E) : ‖φ n x‖ ≤ C := by
    have hqbound : ‖q (a n * t x - 1)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    calc
      ‖φ n x‖ = ‖q (a n * t x - 1)‖ * ‖ψ x‖ := norm_mul _ _
      _ ≤ 1 * A := mul_le_mul hqbound (hval x) (norm_nonneg _) zero_le_one
      _ ≤ C := by dsimp [C]; nlinarith [mul_nonneg hD hB]
  have hφder (n : ℕ) (x : E) : ‖partialDeriv (φ n) i x‖ ≤ C := by
    have hqbound : ‖q (a n * t x - 1)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    have hfirst : ‖q (a n * t x - 1) * partialDeriv ψ i x‖ ≤ B := by
      rw [norm_mul]
      exact (mul_le_mul hqbound (hpart x) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hsecond : ‖(deriv q (a n * t x - 1) * a n *
        t (EuclideanSpace.single i 1)) * ψ x‖ ≤ 2 * D * B := by
      by_cases hi : i = Fin.last m
      · have ht : t (EuclideanSpace.single i 1) = 1 := by
          change (EuclideanSpace.single i (1 : ℝ)) (Fin.last m) = 1
          simp [hi]
        rw [ht, mul_one, norm_mul, norm_mul, Real.norm_of_nonneg (ha n).le]
        by_cases hlo : a n * t x - 1 < 0
        · rw [hz _ hlo, norm_zero, zero_mul, zero_mul]; positivity
        by_cases hhi : 1 < a n * t x - 1
        · rw [ho _ hhi, norm_zero, zero_mul, zero_mul]; positivity
        have htx : 0 ≤ t x := by nlinarith [ha n]
        have hv := hbval hi x
        rw [abs_of_nonneg htx] at hv
        calc
          ‖deriv q (a n * t x - 1)‖ * a n * ‖ψ x‖ ≤ D * a n * (B * t x) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hdq _) (ha n).le) hv
              (norm_nonneg _) (mul_nonneg hD (ha n).le)
          _ ≤ 2 * D * B := by nlinarith [mul_nonneg hD hB,
            mul_le_mul_of_nonneg_left (show a n * t x ≤ 2 by linarith) (mul_nonneg hD hB)]
      · have ht : t (EuclideanSpace.single i 1) = 0 := by
          change (EuclideanSpace.single i (1 : ℝ)) (Fin.last m) = 0
          simp [Ne.symm hi]
        rw [ht, mul_zero, zero_mul, norm_zero]; positivity
    rw [hformula]
    exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans (by dsimp [C]; linarith))
  refine ⟨tsupport ψ, hψ.2.1, C, hC, φ, ?_, ?_, ?_⟩
  · intro n; exact ⟨hsmooth n, hcompact n, hinterior n⟩
  · intro n x
    by_cases hx : x ∈ tsupport ψ
    · simp only [Set.indicator_of_mem hx]
      exact ⟨hφval n x, by rw [BoundaryTestApprox.multi_single]; exact hφder n x⟩
    · have hφzero : φ n x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hsupport n hh))
      have hdzero : partialDeriv (φ n) i x = 0 := by
        unfold partialDeriv
        rw [fderiv_of_notMem_tsupport ℝ (fun hh => hx (hsupport n hh))]
        simp
      simp [Set.indicator_of_notMem hx, hφzero, BoundaryTestApprox.multi_single, hdzero]
  · intro x hx
    have htx : 0 < t x := hx
    have he : ∀ᶠ n : ℕ in atTop, 2 < a n * t x := by
      have htend : Tendsto (fun n : ℕ => a n * t x) atTop atTop :=
        (tendsto_atTop_add_const_right atTop 1
          (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_mul_const htx
      exact htend.eventually (eventually_gt_atTop 2)
    have hev : (fun n => φ n x) =ᶠ[atTop] (fun _ => ψ x) := by
      filter_upwards [he] with n hn
      have hqone : q (a n * t x - 1) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith)
      simp [φ, hqone]
    have hed : (fun n => multiDeriv (φ n) (Pi.single i 1) x) =ᶠ[atTop]
        (fun _ => multiDeriv ψ (Pi.single i 1) x) := by
      filter_upwards [he] with n hn
      rw [BoundaryTestApprox.multi_single, BoundaryTestApprox.multi_single, hformula]
      have hqone : q (a n * t x - 1) = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith)
      rw [hqone, ho _ (by linarith)]
      ring
    exact ⟨tendsto_const_nhds.congr' hev.symm, tendsto_const_nhds.congr' hed.symm⟩
