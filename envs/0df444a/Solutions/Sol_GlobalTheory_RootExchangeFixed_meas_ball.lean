-- Prove2me | solution 1 for GlobalTheory.RootExchangeFixed.meas_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:13.609155+00:00
-- url     : https://prove2.me/submissions/91f7cd9e-4ff5-4ab3-b433-c5fcc3d52dad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space
import Theorems.Thm_GlobalTheory_RootExchangeFixed_ball_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
open GlobalTheory GlobalTheory.RootExchangeFixed
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.RootExchangeFixed
theorem _root_.solution (s : kˣ) : MeasurableSet {x : k | valuation k x ≤ valuation k (s : k)} := by
  rw [ball_eq]
  refine (IsOpen.smul ?_ s).measurableSet
  exact Valuation.isOpen_integer
end GlobalTheory.RootExchangeFixed
