-- Prove2me | solution 1 for GlobalTheory.PosOne.toOne_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:13:24.33054+00:00
-- url     : https://prove2.me/submissions/151ca227-3ff7-4980-9a74-4d8cf1582914

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
theorem _root_.solution (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (p : ℕ) (l : A → ℂ) :
    toOne ν σ (p + 2) l = toOne ν σ (p + 1) (exDown ν (p + 1) σ l) := rfl
end GlobalTheory.PosOne
