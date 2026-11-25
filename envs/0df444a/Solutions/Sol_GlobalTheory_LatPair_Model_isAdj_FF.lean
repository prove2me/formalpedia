-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.isAdj_FF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:38.282319+00:00
-- url     : https://prove2.me/submissions/97560bcf-7da9-4da7-b581-cce154f22a81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_Model_isAdj_sumOp
import Theorems.Thm_GlobalTheory_LatPair_conj_resChar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
namespace GlobalTheory.LatPair.Model
theorem _root_.solution {ψ : AddChar k Circle} (hψ : SplitWeil.HasConductor ψ 1) (q : Unif k) :
    IsAdj (FF q (resChar ψ hψ q) : Module.End ℂ (Form k n ℂ)) (FFStar q (resChar ψ hψ q)) :=
  isAdj_sumOp _ _ _ _ (fun P Q => by simp [eq_comm]) fun P Q _ => by rw [conj_resChar, neg_neg]
end GlobalTheory.LatPair.Model
