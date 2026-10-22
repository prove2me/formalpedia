-- Prove2me | solution 1 for NesterovRCD.Constrained.eq_4_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:39:13.247276+00:00
-- url     : https://prove2.me/submissions/74a1db98-da0a-4ebf-9edb-bed1b63de01d

import Mathlib
import Definitions.Def_NesterovRCD_HighProb_Basic
import Definitions.Def_NesterovRCD_Constrained_UCDM
set_option autoImplicit false

namespace ZZC2

open NesterovRCD.Sublinear

lemma coord_descent {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (f : Blocks E → ℝ) (L : Fin n → ℝ) (hL : CoordLipschitz f L) (i : Fin n)
    (x : Blocks E) (h : E i) :
    f (x + Pi.single i h) ≤ f x + partialGrad f x i h + L i / 2 * ‖h‖ ^ 2 := by
  obtain ⟨hdiff, hpos, hlip⟩ := hL
  set s : Blocks E := Pi.single i h with hs
  set ψ : ℝ → ℝ := fun t => f (x + t • s) - t * partialGrad f x i h - L i / 2 * t ^ 2 * ‖h‖ ^ 2 with hψ
  have hline : ∀ t : ℝ, HasDerivAt (fun r : ℝ => f (x + r • s)) (partialGrad f (x + t • s) i h) t := by
    intro t
    have h1 : HasFDerivAt f (fderiv ℝ f (x + t • s)) (x + t • s) := (hdiff _).hasFDerivAt
    have h2 : HasDerivAt (fun r : ℝ => x + r • s) s t := by
      simpa using ((hasDerivAt_id t).smul_const s).const_add x
    have := h1.comp_hasDerivAt t h2
    have e : partialGrad f (x + t • s) i h = fderiv ℝ f (x + t • s) s := by
      simp [partialGrad, hs]
    rw [e]
    exact this
  have hψd : ∀ t : ℝ, HasDerivAt ψ
      (partialGrad f (x + t • s) i h - partialGrad f x i h - L i * t * ‖h‖ ^ 2) t := by
    intro t
    have h1 := hline t
    have h2 : HasDerivAt (fun r : ℝ => r * partialGrad f x i h) (partialGrad f x i h) t := by
      simpa using (hasDerivAt_id t).mul_const (partialGrad f x i h)
    have h3 : HasDerivAt (fun r : ℝ => L i / 2 * r ^ 2 * ‖h‖ ^ 2) (L i * t * ‖h‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L i / 2)).mul_const (‖h‖ ^ 2)
      exact this.congr_deriv (by first | ring | (norm_num; ring) | norm_num)
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc (0:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hψd t).continuousAt.continuousWithinAt
    · intro t _
      exact (hψd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      have hts : t • s = Pi.single i (t • h) := by
        rw [hs]; ext j; by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_eq_of_ne hj]
      have hl := hlip i x (t • h)
      have hl2 : ‖partialGrad f (x + t • s) i - partialGrad f x i‖ ≤ L i * (t * ‖h‖) := by
        rw [hts]
        calc _ ≤ L i * ‖t • h‖ := hl
          _ = L i * (t * ‖h‖) := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      have hop := (partialGrad f (x + t • s) i - partialGrad f x i).le_opNorm h
      have hop2 : (partialGrad f (x + t • s) i - partialGrad f x i) h ≤ ‖partialGrad f (x + t • s) i - partialGrad f x i‖ * ‖h‖ :=
        (le_abs_self _).trans hop
      have e1 : (partialGrad f (x + t • s) i - partialGrad f x i) h = partialGrad f (x + t • s) i h - partialGrad f x i h := rfl
      have := mul_le_mul_of_nonneg_right hl2 (norm_nonneg h)
      nlinarith
  have h01 := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul] at h01
  nlinarith

end ZZC2

namespace NesterovRCD.Constrained

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

lemma ZZC2_exists (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ) (hLpos : ∀ i, 0 < L i)
    (Q : ∀ i, Set (E i)) (hQc : ∀ i, IsClosed (Q i)) (hQv : ∀ i, Convex ℝ (Q i))
    (hQne : ∀ i, (Q i).Nonempty) (x : NesterovRCD.Sublinear.Blocks E) (i : Fin n) :
    ∃ u, IsBlockUpdate f L Q x i u := by
  set a : E i := (InnerProductSpace.toDual ℝ (E i)).symm (NesterovRCD.Sublinear.partialGrad f x i) with ha
  have hpa : ∀ v, NesterovRCD.Sublinear.partialGrad f x i v = inner ℝ a v := by
    intro v
    simp [ha, InnerProductSpace.toDual_symm_apply]
  have hLi := hLpos i
  set c : E i := x i - (1 / L i) • a with hc
  have hcomp : IsComplete (Q i) := (hQc i).isComplete
  obtain ⟨v, hv, hvmin⟩ := exists_norm_eq_iInf_of_complete_convex (hQne i) hcomp (hQv i) c
  refine ⟨v, hv, fun w hw => ?_⟩
  have hle : ‖c - v‖ ≤ ‖c - w‖ := by
    rw [hvmin]
    exact ciInf_le (⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ : BddBelow (Set.range fun w : Q i => ‖c - (w : E i)‖)) ⟨w, hw⟩
  have key : ∀ z : E i, ‖c - z‖ ^ 2 = ‖z - x i‖ ^ 2 + 2 / L i * inner ℝ a (z - x i) + ‖a‖ ^ 2 / L i ^ 2 := by
    intro z
    have e : c - z = -((z - x i) + (1 / L i) • a) := by simp [hc]; abel
    rw [e, norm_neg, norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm]
    field_simp
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [key v, key w] at h2
  rw [hpa, hpa]
  have : 0 < 2 / L i := by positivity
  have hLi2 : L i / 2 * (2 / L i) = 1 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ L i / 2)]

theorem ZZC2_main (hn : 0 < n) (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (Q : ∀ i, Set (E i)) (hQc : ∀ i, IsClosed (Q i)) (hQv : ∀ i, Convex ℝ (Q i))
    (hQne : ∀ i, (Q i).Nonempty) (x : NesterovRCD.Sublinear.Blocks E) (hx : x ∈ Qset Q) (i : Fin n) :
    L i / 2 * ‖blockUpdate f L Q x i - x i‖ ^ 2 ≤ f x - f (constrStep f L Q i x) := by
  have hLpos : 0 < L i := hL.2.1 i
  have hspec : IsBlockUpdate f L Q x i (blockUpdate f L Q x i) :=
    Classical.epsilon_spec (ZZC2_exists f L hL.2.1 Q hQc hQv hQne x i)
  set u := blockUpdate f L Q x i with hu
  set h : E i := u - x i with hh
  have hxi : x i ∈ Q i := hx i (Set.mem_univ i)
  -- key inequality  f'h + L‖h‖² ≤ 0
  have hkey : NesterovRCD.Sublinear.partialGrad f x i h + L i * ‖h‖ ^ 2 ≤ 0 := by
    have hT : ∀ t : ℝ, 0 < t → t ≤ 1 →
        NesterovRCD.Sublinear.partialGrad f x i h + L i / 2 * (2 - t) * ‖h‖ ^ 2 ≤ 0 := by
      intro t ht0 ht1
      have hut : u + t • (x i - u) ∈ Q i := by
        have := (hQv i) hspec.1 hxi (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
        convert this using 1
        module
      have hm := hspec.2 _ hut
      have e : u + t • (x i - u) - x i = (1 - t) • h := by
        simp only [hh]; module
      rw [e, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - t)] at hm
      simp only [smul_eq_mul] at hm
      have : t * (NesterovRCD.Sublinear.partialGrad f x i h + L i / 2 * (2 - t) * ‖h‖ ^ 2) ≤ 0 := by
        nlinarith
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_pos ht0 hcon]
    by_contra hcon
    push_neg at hcon
    set a := NesterovRCD.Sublinear.partialGrad f x i h + L i * ‖h‖ ^ 2 with ha
    have hapos : 0 < a := hcon
    set t := min 1 (a / (L i * ‖h‖ ^ 2 + 1)) with htdef
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ a / (L i * ‖h‖ ^ 2 + 1) := min_le_right _ _
    have h1 := hT t ht0 ht1
    have hB : 0 < L i * ‖h‖ ^ 2 + 1 := by positivity
    have h3 : t * (L i * ‖h‖ ^ 2 + 1) ≤ a := by
      have := mul_le_mul_of_nonneg_right ht2 hB.le
      rwa [div_mul_cancel₀ _ hB.ne'] at this
    nlinarith [mul_nonneg ht0.le (sq_nonneg ‖h‖), mul_pos hLpos ht0]
  have hd := ZZC2.coord_descent f L hL i x h
  have : constrStep f L Q i x = x + Pi.single i h := rfl
  rw [this]
  nlinarith
end NesterovRCD.Constrained

theorem solution {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] (hn : 0 < n) (f : NesterovRCD.Sublinear.Blocks E → ℝ) (L : Fin n → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hL : NesterovRCD.Sublinear.CoordLipschitz f L)
    (Q : ∀ i, Set (E i)) (hQc : ∀ i, IsClosed (Q i)) (hQv : ∀ i, Convex ℝ (Q i))
    (hQne : ∀ i, (Q i).Nonempty) (x : NesterovRCD.Sublinear.Blocks E) (hx : x ∈ NesterovRCD.Constrained.Qset Q) (i : Fin n) :
    L i / 2 * ‖NesterovRCD.Constrained.blockUpdate f L Q x i - x i‖ ^ 2 ≤ f x - f (NesterovRCD.Constrained.constrStep f L Q i x) :=
  NesterovRCD.Constrained.ZZC2_main hn f L hf hL Q hQc hQv hQne x hx i
