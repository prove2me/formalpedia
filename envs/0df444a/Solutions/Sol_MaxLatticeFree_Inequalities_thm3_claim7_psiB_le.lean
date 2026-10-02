-- Prove2me | solution 1 for MaxLatticeFree.Inequalities.thm3_claim7_psiB_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:33:17.056978+00:00
-- url     : https://prove2.me/submissions/ead92361-d11d-47db-b575-8a56fd04c489

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_LatticeFree
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities
import Definitions.Def_MaxLatticeFree_Inequalities_Polar

set_option autoImplicit false

open scoped RealInnerProductSpace in
open MaxLatticeFree.Inequalities in
/-- If `B ⊇ B_ψ` and `ψ` is positively homogeneous, then every `y ∈ (B - f)*` satisfies
`c ⟪r, y⟫ ≤ 1` whenever `c ≥ 0` and `c ψ(r) ≤ 1`. -/
theorem p2fe33b69_scaled_le {q : ℕ} (f : EuclideanSpace ℝ (Fin q))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (ψ : W → ℝ)
    (hph : IsPositivelyHomogeneous ψ)
    (B : Set (EuclideanSpace ℝ (Fin q))) (hBB : Bpsi f W ψ 1 ⊆ B)
    (y : EuclideanSpace ℝ (Fin q)) (hy : y ∈ polarW W ((fun x => x - f) '' B))
    (r : W) (c : ℝ) (hc : 0 ≤ c) (hcr : c * ψ r ≤ 1) :
    c * ⟪(r : EuclideanSpace ℝ (Fin q)), y⟫ ≤ 1 := by
  have hmem : (f + c • (r : EuclideanSpace ℝ (Fin q))) - f ∈ W := by
    rw [add_sub_cancel_left]
    exact W.smul_mem c r.2
  have hx : f + c • (r : EuclideanSpace ℝ (Fin q)) ∈ B := by
    apply hBB
    refine ⟨hmem, ?_⟩
    have heq : (⟨(f + c • (r : EuclideanSpace ℝ (Fin q))) - f, hmem⟩ : W) = c • r := by
      apply Subtype.ext
      simp
    rw [heq, hph r c hc]
    exact hcr
  have h1 := hy.2 _ ⟨_, hx, rfl⟩
  simp only at h1
  rw [add_sub_cancel_left, real_inner_smul_left] at h1
  exact h1

open MaxLatticeFree.Inequalities in
theorem solution {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) (ψ'' : W → ℝ)
    (hsub : IsSublinear ψ'') (hnonneg : ∀ r, 0 ≤ ψ'' r) (hvalid : IsValid f W ψ'' 1)
    (B : Set (EuclideanSpace ℝ (Fin q))) (hB : IsMaximalLatticeFree f W B) (hBB : Bpsi f W ψ'' 1 ⊆ B) :
    ∀ r : W, psiB f W B r ≤ ψ'' r := by
  intro r
  unfold psiB rhoK
  apply Real.sSup_le _ (hnonneg r)
  rintro _ ⟨y, hy, rfl⟩
  have key := p2fe33b69_scaled_le f W ψ'' hsub.1 B hBB y hy.1 r
  dsimp only
  rcases (hnonneg r).lt_or_eq with hpos | hzero
  · have h := key (ψ'' r)⁻¹ (inv_nonneg.mpr hpos.le) (by rw [inv_mul_cancel₀ hpos.ne'])
    rw [inv_mul_le_iff₀ hpos, mul_one] at h
    exact h
  · rw [← hzero]
    by_contra hcon
    rw [not_le] at hcon
    have h := key (2 / inner ℝ (r : EuclideanSpace ℝ (Fin q)) y) (by positivity)
      (by rw [← hzero, mul_zero]; norm_num)
    rw [div_mul_cancel₀ _ hcon.ne'] at h
    norm_num at h
