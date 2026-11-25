-- Prove2me | solution 1 for GlobalTheory.StepData.extZ_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:14:41.745633+00:00
-- url     : https://prove2.me/submissions/dfacf7a0-9112-4473-b2f3-a2e4c43fd5a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData
theorem _root_.solution (J : Subgroup (GL a k)) (ρ : J →* ℂˣ) (g g' : J) :
    extZ J ρ ((g : GL a k).val * (g' : GL a k).val) = extZ J ρ (g : GL a k).val * ρ g' := by
  rw [extZ_coe, ← Units.val_mul, ← Subgroup.coe_mul, extZ_coe, map_mul, Units.val_mul]
end GlobalTheory.StepData
