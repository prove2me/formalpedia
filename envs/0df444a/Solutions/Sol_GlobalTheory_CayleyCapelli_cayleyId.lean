-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.cayleyId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:10:51.96204+00:00
-- url     : https://prove2.me/submissions/21b6fa3a-40eb-40bb-a132-56ef623e3796

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Theorems.Thm_GlobalTheory_CayleyCapelli_pair_diffOp
import Theorems.Thm_GlobalTheory_CayleyCapelli_eq_of_pair
import Theorems.Thm_GlobalTheory_CayleyCapelli_pair_detL_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open GlobalTheory GlobalTheory.CayleyCapelli
open MvPolynomial Formalism.IncomingBounds ReciprocityTheory.PGsh GlobalTheory.DetPowPairing
variable {σ : Type} {C : Type} [Field C]
namespace GlobalTheory.CayleyCapelli
theorem _root_.solution : CayleyId := by
  intro K _ _ n s
  refine eq_of_pair fun B => ?_
  rw [pair_diffOp, pair_detL_pow, map_smul, smul_eq_mul]
  push_cast
  rfl
end GlobalTheory.CayleyCapelli
