-- Prove2me | solution 1 for GlobalTheory.T.exists_finset_integralScaledBoxPi_coset_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:18:39.783806+00:00
-- url     : https://prove2.me/submissions/5a9c2f1c-b08f-4b57-af81-780f4604823a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetIntegralScaledBoxPiCosetReps
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetIntegralScaledBoxPiCosetRepsStatement
import Theorems.Thm_GlobalTheory_BoxReps_exists_finset_box_reps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ), valuation k (r : k) ≤ valuation k (R : k) → ∃ S : Finset (n → k), (∀ b ∈ S, b ∈ box n R) ∧ ∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r := by
  first | exact @GlobalTheory.BoxReps.exists_finset_box_reps | exact GlobalTheory.BoxReps.exists_finset_box_reps | (intros; apply GlobalTheory.BoxReps.exists_finset_box_reps <;> assumption)
end _root_.GlobalTheory.T
