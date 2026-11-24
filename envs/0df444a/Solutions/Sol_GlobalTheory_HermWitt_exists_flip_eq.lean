-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_flip_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:23:31.952219+00:00
-- url     : https://prove2.me/submissions/fc9c0f24-50bc-49c9-b238-7f33dc4aa925

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_fin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
namespace GlobalTheory.HermWitt
theorem _root_.solution [FiniteDimensional E V] (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) (ψ : V →ₗ[E] E) : ∃ w, ∀ z, B z w = ψ z := by
  obtain ⟨v, hv⟩ := exists_orthogonal_basis_fin h2 (finrank E V) B hB rfl
  have hne : ∀ i, B (v i) (v i) ≠ 0 := fun i hi => v.ne_zero i (hV _ fun b => by
    have : B.flip (v i) = 0 := v.ext fun j => by
      by_cases hij : j = i
      · subst hij
        exact hi
      · exact hv j i hij
    exact LinearMap.congr_fun this b)
  refine ⟨∑ i, c (ψ (v i) / B (v i) (v i)) • v i, fun z => ?_⟩
  have : B.flip (∑ i, c (ψ (v i) / B (v i) (v i)) • v i) = ψ := v.ext fun j => by
    rw [LinearMap.flip_apply, map_sum, Finset.sum_eq_single j]
    · rw [LinearMap.map_smulₛₗ, hc, smul_eq_mul, div_mul_cancel₀ _ (hne j)]
    · intro i _ hij
      rw [LinearMap.map_smulₛₗ, hv j i hij.symm, smul_zero]
    · simp
  exact LinearMap.congr_fun this z
end GlobalTheory.HermWitt
