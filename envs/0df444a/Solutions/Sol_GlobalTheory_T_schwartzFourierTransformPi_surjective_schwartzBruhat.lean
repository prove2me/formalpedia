-- Prove2me | solution 1 for GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:11:48.554096+00:00
-- url     : https://prove2.me/submissions/71d4874e-a02a-45f8-bb50-8be77735ba21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzFourierTransformPiSurjectiveSchwartzBruh
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzFourierTransformPiSurjectiveSchwartzBruhStatement
import Theorems.Thm_GlobalTheory_SplitWeil_FourierSurj_hat_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), (∀ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 ∈ SB (n → k)) ∧ ∀ g : SB (n → k), ∃ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 = g.1 := by
  first | exact @GlobalTheory.SplitWeil.FourierSurj.hat_surjective | exact GlobalTheory.SplitWeil.FourierSurj.hat_surjective | (intros; apply GlobalTheory.SplitWeil.FourierSurj.hat_surjective <;> assumption)
end _root_.GlobalTheory.T
