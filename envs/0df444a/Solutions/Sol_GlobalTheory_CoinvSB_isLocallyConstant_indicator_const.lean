-- Prove2me | solution 1 for GlobalTheory.CoinvSB.isLocallyConstant_indicator_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:30:35.84109+00:00
-- url     : https://prove2.me/submissions/a67d7c10-9769-44cf-b865-bc739b8da147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralLastFactorSliceMemSchwartzBruhatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsCutoffOfAddCharTranslationInvariantFunctioStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatFunctionalZeroOfFibreIntegralZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatLinearFunctional

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
noncomputable section
open GlobalTheory GlobalTheory.CoinvSB
namespace GlobalTheory.CoinvSB
theorem _root_.solution {X : Type*} [TopologicalSpace X] {U : Set X} (h1 : IsOpen U)
    (h2 : IsClosed U) (c : ℂ) : IsLocallyConstant (U.indicator fun _ => c) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  by_cases hx : x ∈ U
  · filter_upwards [h1.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  · filter_upwards [h2.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
end GlobalTheory.CoinvSB
