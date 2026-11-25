-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage.isUnramUnitary_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:52:58.393362+00:00
-- url     : https://prove2.me/submissions/bfdedaef-9502-4e6e-b3eb-711f6d57d8bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {P P' A A' : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
variable [MeasurableSpace k] [BorelSpace k]
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
theorem _root_.solution : IsUnramUnitary (1 : kˣ →* ℂˣ) := ⟨fun _ _ => rfl, fun _ => by simp⟩
end GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
