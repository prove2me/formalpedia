-- Prove2me | solution 1 for GlobalTheory.box_subset_box_of_valuation_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:24:36.200133+00:00
-- url     : https://prove2.me/submissions/94efded2-5b70-4b84-9a37-b4049e5941ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsIntegralScaledBoxPiSupersetOfIsCompact

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) {s t : kˣ}
    (h : valuation k (s : k) ≤ valuation k (t : k)) : box n s ⊆ box n t :=
  fun x hx i _ => show valuation k (x i) ≤ _ from le_trans (hx i trivial) h
end GlobalTheory
