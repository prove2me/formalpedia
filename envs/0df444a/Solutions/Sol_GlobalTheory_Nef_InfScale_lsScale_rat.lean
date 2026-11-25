-- Prove2me | solution 1 for GlobalTheory.Nef.InfScale.lsScale_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:25:27.670271+00:00
-- url     : https://prove2.me/submissions/021fba4f-b928-4068-93c4-4fc6c27763f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsScalingCompatibleExpansionAtInfinity
import Theorems.Thm_GlobalTheory_Nef_InfScale_lsScale_comp
import Theorems.Thm_GlobalTheory_Nef_InfScale_ext_rat
import Theorems.Thm_GlobalTheory_Nef_InfScale_ratScale_C
import Theorems.Thm_GlobalTheory_Nef_InfScale_ratScale_X
import Theorems.Thm_GlobalTheory_Nef_InfScale_alg_C
import Theorems.Thm_GlobalTheory_Nef_InfScale_alg_X
import Theorems.Thm_P2M_GlobalTheory_Nef_InfScale_rescale_C__71b0224c35f6
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.InfScale
variable {F : Type} [Field F]
namespace GlobalTheory.Nef.InfScale
theorem _root_.solution (c : F) (hc : c ≠ 0) :
    (lsScale c hc).comp (algebraMap (RatFunc F) (LaurentSeries F)) =
      (algebraMap (RatFunc F) (LaurentSeries F)).comp (ratScale c hc) := by
  have hl : ∀ p, lsScale c hc (algebraMap (PowerSeries F) (LaurentSeries F) p) =
      algebraMap (PowerSeries F) (LaurentSeries F) (PowerSeries.rescale c p) :=
    fun p => RingHom.congr_fun (lsScale_comp c hc) p
  apply ext_rat
  · intro a
    simp only [RingHom.comp_apply, ratScale_C, alg_C, hl, rescale_C']
  · simp only [RingHom.comp_apply, ratScale_X, map_mul, alg_C, alg_X, hl, PowerSeries.rescale_X,
      rescale_C']
end GlobalTheory.Nef.InfScale
