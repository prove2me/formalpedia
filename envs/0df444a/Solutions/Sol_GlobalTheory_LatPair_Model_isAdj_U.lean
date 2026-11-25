-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.isAdj_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:42.161502+00:00
-- url     : https://prove2.me/submissions/09e65d32-4e0e-47fc-afb2-66f313782820

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_Model_isAdj_sumOp

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
theorem _root_.solution (q : Unif k) : IsAdj (U q : Module.End ℂ (Form k n ℂ)) (D q) :=
  isAdj_sumOp _ _ _ _ (fun P Q => by simp [eq_comm]) fun P Q _ => by simp
end GlobalTheory.LatPair.Model
