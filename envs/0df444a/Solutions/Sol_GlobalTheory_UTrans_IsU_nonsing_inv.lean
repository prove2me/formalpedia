-- Prove2me | solution 1 for GlobalTheory.UTrans.IsU.nonsing_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:20.147932+00:00
-- url     : https://prove2.me/submissions/ea37d311-44fc-476a-9823-0e7cd4d88b4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Theorems.Thm_GlobalTheory_UTrans_IsU_det_mul_conj_det

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
open GlobalTheory GlobalTheory.UTrans
namespace GlobalTheory.UTrans
namespace IsU
theorem _root_.solution {E : Type} [Field E] {n : ℕ} {σ : E →+* E}
    {G γ : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (h : IsU σ G γ) : IsU σ G γ⁻¹ := by
  have hu : IsUnit γ.det := IsUnit.of_mul_eq_one _ (h.det_mul_conj_det hG)
  intro x y
  rw [← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec, Matrix.one_mulVec]
end IsU
end GlobalTheory.UTrans
