-- Prove2me | solution 1 for GlobalTheory.tensorToModP_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:53.837797+00:00
-- url     : https://prove2.me/submissions/e9b6585e-7ca2-46fe-bfe8-fe8c66ac4c53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex
import Theorems.Thm_GlobalTheory_modPPairing_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (p : ℕ) (M : ModuleCat.{0} ℤ) (m : M) :
    tensorToModP p M
      (((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom m) =
      Submodule.Quotient.mk m := by
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  unfold tensorToModP
  exact (TensorProduct.liftAddHom_tmul _ _ _ _).trans (modPPairing_one p M m)
end GlobalTheory
