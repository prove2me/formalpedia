-- Prove2me | solution 1 for GlobalTheory.SplitDict.bijOn_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:41.552631+00:00
-- url     : https://prove2.me/submissions/035f2268-4873-4942-b851-3e73b40e91c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {T : Type} [TopologicalSpace T] [T2Space T]
variable {ψ : AddChar k Circle} {c : kˣ}
namespace GlobalTheory.SplitDict
theorem _root_.solution {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Set.BijOn (fun f : Y → ℂ => f ∘ e) {f | f ∈ SB Y} {f | f ∈ SB X} := by
  refine ⟨fun f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩,
    fun f _ g _ hfg => ?_, fun g hg => ⟨g ∘ e.symm, ⟨hg.1.comp_continuous e.symm.continuous,
      hg.2.comp_homeomorph e.symm⟩, ?_⟩⟩
  · funext y
    simpa using congrFun hfg (e.symm y)
  · funext x
    simp
end GlobalTheory.SplitDict
