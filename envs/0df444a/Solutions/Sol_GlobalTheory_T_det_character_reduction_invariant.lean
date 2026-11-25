-- Prove2me | solution 1 for GlobalTheory.T.det_character_reduction_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:17:46.717301+00:00
-- url     : https://prove2.me/submissions/e6040387-eb63-49f5-a71a-5680e9400ece

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetCharacterReductionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetCharacterReductionInvariantStatement
import Theorems.Thm_GlobalTheory_char_eq_one_of_inverse_reduction_det_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (L L' : Type) [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L'] [Module.Finite R L'] [Module.Projective R L'] (I : Ideal R) [Finite (R ⧸ I)] (A : Type) [CommGroup A] (ψ : ((L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (L ⧸ (I • ⊤ : Submodule R L))) →* A) (t : L →ₗ[R] L') (γ : L' →ₗ[R] L') (k : (L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (L ⧸ (I • ⊤ : Submodule R L))), (∀ 𝔪 : Ideal (R ⧸ I), 𝔪.IsMaximal → 4 ≤ Nat.card ((R ⧸ I) ⧸ 𝔪)) → (∀ b, ∃ a, b - t a ∈ (I • ⊤ : Submodule R L')) → (∀ a, t a ∈ (I • ⊤ : Submodule R L') → a ∈ (I • ⊤ : Submodule R L)) → LinearMap.det (LinearMap.baseChange (R ⧸ I) γ) = 1 → (∀ a, ∃ a', (Submodule.Quotient.mk a' : L ⧸ (I • ⊤ : Submodule R L)) = k (Submodule.Quotient.mk a) ∧ γ (t a') - t a ∈ (I • ⊤ : Submodule R L')) → ψ k = 1 := by
  first | exact @GlobalTheory.char_eq_one_of_inverse_reduction_det_one | exact GlobalTheory.char_eq_one_of_inverse_reduction_det_one | (intros; apply GlobalTheory.char_eq_one_of_inverse_reduction_det_one <;> assumption)
end _root_.GlobalTheory.T
