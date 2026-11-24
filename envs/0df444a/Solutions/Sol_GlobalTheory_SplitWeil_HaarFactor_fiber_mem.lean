-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HaarFactor.fiber_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:20.59917+00:00
-- url     : https://prove2.me/submissions/6c43996e-2db3-4574-93cb-ea2f11e938a6

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
variable {X₀ A : Type*} [TopologicalSpace X₀] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [T2Space X₀] [T2Space A]
namespace GlobalTheory.SplitWeil.HaarFactor
theorem _root_.solution {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A)) (x : X₀) : (fun a => G (x, a)) ∈ SB A := by
  refine ⟨hG.1.comp_continuous (by fun_prop), HasCompactSupport.intro (hG.2.image continuous_snd) fun a ha => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun h => ha ⟨(x, a), h, rfl⟩
end GlobalTheory.SplitWeil.HaarFactor
