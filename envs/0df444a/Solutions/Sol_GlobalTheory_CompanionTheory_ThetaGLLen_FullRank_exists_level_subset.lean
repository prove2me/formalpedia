-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_level_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:13.995194+00:00
-- url     : https://prove2.me/submissions/32eccd3c-9a2f-4f29-8669-5725a53e9f5e

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
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [TotallyDisconnectedSpace H] (K : Subgroup H), IsCompact (K : Set H) → IsOpen (K : Set H) → ∀ U ∈ 𝓝 (1 : H), ∃ N : Subgroup H, IsOpen (N : Set H) ∧ N ≤ K ∧ (N : Set H) ⊆ U ∧ ∀ κ ∈ K, ∀ n ∈ N, κ * n * κ⁻¹ ∈ N := by
  intro H _ _ _ _ _ K hKc hKo U hU
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hVo : IsOpen ((Subtype.val : K → H) ⁻¹' interior U) := isOpen_interior.preimage continuous_subtype_val
  have h1 : (1 : K) ∈ (Subtype.val : K → H) ⁻¹' interior U := mem_interior_iff_mem_nhds.2 hU
  obtain ⟨M, hM⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVo h1
  refine ⟨M.toSubgroup.map K.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact hKo.isOpenEmbedding_subtypeVal.isOpenMap _ M.isOpen'
  · rintro _ ⟨m, hm, rfl⟩
    exact interior_subset (hM hm)
  · rintro κ hκ _ ⟨m, hm, rfl⟩
    exact ⟨⟨κ, hκ⟩ * m * (⟨κ, hκ⟩ : K)⁻¹, M.isNormal'.conj_mem m hm _, by simp⟩
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
