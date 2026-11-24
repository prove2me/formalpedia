-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_indicator_orb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:16.108769+00:00
-- url     : https://prove2.me/submissions/6a3f9576-8c47-42a5-b311-5d8d091e62e4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_SBExtend_indicator_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_Model_indicator_mem_SB


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
variable {H X : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace X] [MulAction H X]
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution [T2Space X] [ContinuousSMul H X] (hopen : ∀ x : X, IsOpenMap fun g : H => g • x)
    {K N : Subgroup H} (hK : IsCompact (K : Set H)) (hN : IsLevel K N) (x₀ : X) :
    ∃ v : SB X, ∀ x, v.1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) x := by
  have hc : IsCompact (N : Set H) :=
    hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hN.1) hN.2.1
  have hc' : IsCompact (orb N x₀) := hc.image (continuous_id.smul continuous_const)
  exact ⟨⟨_, GlobalTheory.SBExtend.indicator_mem_SB hc' ⟨hc'.isClosed, hopen x₀ _ hN.1⟩⟩, fun _ => rfl⟩
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
