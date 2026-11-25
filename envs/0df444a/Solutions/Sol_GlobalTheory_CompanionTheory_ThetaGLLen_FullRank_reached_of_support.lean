-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.reached_of_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:44.347431+00:00
-- url     : https://prove2.me/submissions/2f07a933-07b1-4318-8d43-3f5b25c29ee5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_nhds_smul_invariant
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_level_subset
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_indicator_orb
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_mem_span_translates_of_level

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
variable [T2Space X] [ContinuousSMul H X]
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution [T2Space H] [TotallyDisconnectedSpace H] (ρ : Representation ℂ H (SB X))
    (hρ : ∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x))
    (hopen : ∀ x : X, IsOpenMap fun g : H => g • x) {K : Subgroup H} (hK : IsCompact (K : Set H))
    (hKo : IsOpen (K : Set H)) (x₀ : X) (f : SB X) (hf : ∀ x, f.1 x ≠ 0 → x ∈ orb K x₀) :
    Reached ρ K x₀ f := by
  obtain ⟨U, hU, hUf⟩ := exists_nhds_smul_invariant H X f
  obtain ⟨N, hNo, hNK, hNU, hNn⟩ := exists_level_subset H K hK hKo U hU
  have hN : IsLevel K N := ⟨hNo, hNK, hNn⟩
  obtain ⟨v, hv⟩ := exists_indicator_orb hopen hK hN x₀
  exact ⟨N, hN, v, hv, mem_span_translates_of_level H X ρ hρ K N hK hNo hNK hNn x₀ v f hv (fun n hn x => hUf n (hNU hn) x) hf⟩
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
