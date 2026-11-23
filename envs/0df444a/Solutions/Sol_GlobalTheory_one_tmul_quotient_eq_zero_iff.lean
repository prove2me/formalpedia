-- Prove2me | solution 1 for GlobalTheory.one_tmul_quotient_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:21.646228+00:00
-- url     : https://prove2.me/submissions/15d2c31b-f332-4e41-9bce-ffa2b35884f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct
variable {R : Type*} [CommRing R] (I : Ideal R)
namespace GlobalTheory
theorem _root_.solution (J : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    (x : M) : (1 : R ⧸ J) ⊗ₜ[R] x = 0 ↔ x ∈ (J • ⊤ : Submodule R M) := by
  rw [← (quotTensorEquivQuotSMul M J).map_eq_zero_iff, quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.Quotient.mk_eq_zero]
end GlobalTheory
