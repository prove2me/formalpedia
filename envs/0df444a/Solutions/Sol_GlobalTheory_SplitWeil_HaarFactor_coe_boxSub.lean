-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HaarFactor.coe_boxSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:08.260478+00:00
-- url     : https://prove2.me/submissions/59c892f6-f182-4b2c-b89e-2f3dad4646d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.HaarFactor
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitWeil.HaarFactor
theorem _root_.solution (n : Type*) (s : kˣ) : (boxSub n s : Set (n → k)) = FourierPi.box n s := by
  ext x
  simp only [SetLike.mem_coe, boxSub, AddSubgroup.mem_pi, FourierPi.box, Set.mem_pi]
  rfl
end GlobalTheory.SplitWeil.HaarFactor
