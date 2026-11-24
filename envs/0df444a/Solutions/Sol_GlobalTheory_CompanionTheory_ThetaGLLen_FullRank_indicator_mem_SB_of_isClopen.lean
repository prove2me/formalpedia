-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.indicator_mem_SB_of_isClopen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:16.601812+00:00
-- url     : https://prove2.me/submissions/397bab2f-fadd-4dbb-b3a8-66f6a3db1f07

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution {X : Type} [TopologicalSpace X] {Y : Set X} (hY : IsClopen Y) (f : SB X) :
    Y.indicator f.1 ∈ SB X := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, HasCompactSupport.mono f.2.2 fun x hx => ?_⟩
  · have hf := (IsLocallyConstant.iff_eventually_eq _).1 f.2.1 x
    by_cases hx : x ∈ Y
    · filter_upwards [hY.isOpen.mem_nhds hx, hf] with y hy e
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, e]
    · filter_upwards [hY.compl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · by_cases h : x ∈ Y
    · rw [Function.mem_support, Set.indicator_of_mem h] at hx
      exact hx
    · exact absurd (Set.indicator_of_notMem h _) hx
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
