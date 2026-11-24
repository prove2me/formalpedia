-- Prove2me | solution 1 for GlobalTheory.SplitDict.slice_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:45.714001+00:00
-- url     : https://prove2.me/submissions/2ef16245-eafc-4b4c-9a38-c6d3cd9482ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


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
omit [DecidableEq n] [T2Space T] [Fintype n]
namespace GlobalTheory.SplitDict
theorem _root_.solution {f : T × (n → k) → ℂ} (hf : f ∈ SB (T × (n → k))) (t : T) :
    (fun x => f (t, x)) ∈ SB (n → k) := by
  haveI := t2Space k
  refine ⟨hf.1.comp_continuous (by fun_prop),
    HasCompactSupport.intro (hf.2.isCompact.image continuous_snd) fun x hx => ?_⟩
  exact image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩
end GlobalTheory.SplitDict
