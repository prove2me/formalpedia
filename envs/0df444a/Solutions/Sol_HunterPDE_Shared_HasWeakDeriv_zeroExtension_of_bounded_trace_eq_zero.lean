-- Prove2me | solution 1 for HunterPDE.Shared.HasWeakDeriv.zeroExtension_of_bounded_trace_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T17:19:21.388234+00:00
-- url     : https://prove2.me/submissions/0fb1b9a9-ad7a-41d5-81bb-ccb90cf076f9

import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_integral_mul_bounded_trace_normal
import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_integral_mul_boundaryCompatible
import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_ae_eq
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open MeasureTheory HunterPDE.Compactness HunterPDE.Shared
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (C : ℝ≥0) (T : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hlinear : (∀ f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        MemW 1 p (upperHalfSpace m) f → MemW 1 p (upperHalfSpace m) g → ∀ a b : ℝ,
          T (a • f + b • g) =ᵐ[volume] a • T f + b • T g))
    (hbound : (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        MemLp (T f) p volume ∧
          eLpNorm (T f) p volume ≤ (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f))
    (hsmooth : (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, IsSmoothCompactClosedHalfSpace f →
        T f =ᵐ[volume] fun x' => f (boundaryPoint x')))
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (hf : MemW 1 p (upperHalfSpace m) f)
    (hzero : T f =ᵐ[volume] 0)
    (α : Fin (m + 1) → ℕ) (hα : ∑ i, α i ≤ 1)
    (g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hg : HunterPDE.Shared.HasWeakDeriv (upperHalfSpace m) α f g)
    (hgp : MemLp g p (volume.restrict (upperHalfSpace m))) :
    HunterPDE.Shared.HasWeakDeriv Set.univ α
      ((upperHalfSpace m).indicator f) ((upperHalfSpace m).indicator g) := by
  classical
  have hH : IsOpen (upperHalfSpace m) :=
    isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last m)).continuous
  have hzmem : (fun _ : Fin (m + 1) => 0) ∈ multiIndicesLe (m + 1) 1 := by
    simp [multiIndicesLe, Fintype.mem_piFinset]
  obtain ⟨g₀, hg₀, hg₀p⟩ := hf _ hzmem
  have hzderiv (ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) :
      multiDeriv ψ (fun _ => 0) = ψ := by
    have hl : multiIndexList (fun _ : Fin (m + 1) => 0) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      simp
    simp only [multiDeriv, hl, iteratedPartial]
  have hself : HunterPDE.Shared.HasWeakDeriv (upperHalfSpace m) (fun _ => 0) f f := by
    refine ⟨hg₀.1, hg₀.1, ?_⟩
    intro ψ hψ
    simp [hzderiv]
  have hfp : MemLp f p (volume.restrict (upperHalfSpace m)) :=
    hg₀p.ae_eq (hg₀.ae_eq hH hself)
  have hF := (memLp_indicator_iff_restrict hH.measurableSet).2 hfp
  have hG := (memLp_indicator_iff_restrict hH.measurableSet).2 hgp
  refine ⟨(hF.locallyIntegrable hp).locallyIntegrableOn _,
    (hG.locallyIntegrable hp).locallyIntegrableOn _, ?_⟩
  intro ψ hψ
  simp only [Measure.restrict_univ]
  have hind (u v : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) :
      (∫ x, (upperHalfSpace m).indicator u x * v x) =
        ∫ x in upperHalfSpace m, u x * v x := by
    rw [← integral_indicator hH.measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ upperHalfSpace m <;> simp [hx]
  rw [hind, hind]
  by_cases ha0 : α = 0
  · subst α
    have heq := hg.ae_eq hH hself
    simp only [Pi.zero_apply, Finset.sum_const_zero, pow_zero, one_mul]
    rw [show multiDeriv ψ (0 : Fin (m + 1) → ℕ) = ψ from hzderiv ψ]
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  · have hex : ∃ i, α i ≠ 0 := by
      by_contra hh
      apply ha0
      ext i
      simpa using (not_exists.mp hh i)
    obtain ⟨i, hi⟩ := hex
    have hone : ∀ j, α j ≠ 0 → i = j ∧ α i = 1 := by
      intro j hj
      exact (Finset.sum_le_one_iff.mp hα) i j (Finset.mem_univ _) (Finset.mem_univ _) hi hj
    have hai : α = Pi.single i 1 := by
      ext j
      by_cases hij : i = j
      · subst j
        simp [(hone i hi).2]
      · have hj : α j = 0 := by
          by_contra hj
          exact hij (hone j hj).1
        simp [hij, hj]
    subst α
    have hsum : ∑ j : Fin (m + 1), Pi.single i (1 : ℕ) j = 1 := by simp
    rw [hsum]
    simp only [pow_one, neg_mul, one_mul]
    by_cases hin : i = Fin.last m
    · subst i
      have hb : (∫ x', T f x' * ψ (boundaryPoint x')) = 0 := by
        have hh : (fun x' => T f x' * ψ (boundaryPoint x')) =ᵐ[volume] 0 := by
          filter_upwards [hzero] with x hx
          simp [hx]
        rw [integral_congr_ae hh]
        simp
      simpa only [hb, sub_zero] using
        HunterPDE.Shared.HasWeakDeriv.integral_mul_bounded_trace_normal
          hp hp' C T hlinear hbound hsmooth f hf g hg hgp ψ hψ
    · exact HunterPDE.Shared.HasWeakDeriv.integral_mul_boundaryCompatible
        m i f g ψ (hfp.locallyIntegrable hp) (hgp.locallyIntegrable hp) hg hψ
        (fun h => (hin h).elim)
