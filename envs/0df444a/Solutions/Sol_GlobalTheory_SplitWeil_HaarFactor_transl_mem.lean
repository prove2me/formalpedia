-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HaarFactor.transl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:08.938574+00:00
-- url     : https://prove2.me/submissions/37637985-1b10-4a96-80ee-f35697fa2cc5

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
theorem _root_.solution {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A)) (c : A) :
    (fun z : X₀ × A => G (z.1, z.2 - c)) ∈ SB (X₀ × A) := by
  refine ⟨hG.1.comp_continuous (by fun_prop), ?_⟩
  exact hG.2.comp_homeomorph ((Homeomorph.refl X₀).prodCongr (Homeomorph.subRight c))
end GlobalTheory.SplitWeil.HaarFactor
