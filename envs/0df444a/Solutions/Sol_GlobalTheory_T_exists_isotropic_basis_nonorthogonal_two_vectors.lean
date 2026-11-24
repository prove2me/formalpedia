-- Prove2me | solution 1 for GlobalTheory.T.exists_isotropic_basis_nonorthogonal_two_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:29:08.015434+00:00
-- url     : https://prove2.me/submissions/f7829d1a-2c85-4576-9422-eec2c01590bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectorsStatement
import Theorems.Thm_GlobalTheory_UTrans_IsoBasis_exists_isotropic_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) → ∀ x y : Fin n → E, x ≠ 0 → y ≠ 0 → ∃ z : Fin n → Fin n → E, LinearIndependent E z ∧ ∀ i, hf σ G (z i) (z i) = 0 ∧ hf σ G x (z i) ≠ 0 ∧ hf σ G y (z i) ≠ 0 := by
  first | exact @GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis | exact GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis | (intros; apply GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis <;> assumption)
end _root_.GlobalTheory.T
