-- Prove2me | solution 1 for GlobalTheory.PosOne.toOne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:12.158286+00:00
-- url     : https://prove2.me/submissions/bedfc602-811f-4d5e-8ecf-d46073b7b8d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.PosOne
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ)
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.PosOne
theorem _root_.solution (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (l : A → ℂ) : toOne ν σ 1 l = l := rfl
end GlobalTheory.PosOne
