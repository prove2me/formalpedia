-- Prove2me | solution 1 for GlobalTheory.CayleyInv.one_add_cayley_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:27.864936+00:00
-- url     : https://prove2.me/submissions/5256063a-a236-450b-8bad-d7bfabf7d1a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutive
import Theorems.Thm_GlobalTheory_CayleyInv_one_add_cayley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.CayleyInv
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.CayleyInv
theorem _root_.solution (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) (c : R)
    (hc : 2 * c = 1) : (1 + (1 - g) * (1 + g)⁻¹) * (c • (1 + g)) = 1 := by
  rw [one_add_cayley g h, smul_mul_smul_comm, hc, one_smul, Matrix.nonsing_inv_mul _ h]
end GlobalTheory.CayleyInv
