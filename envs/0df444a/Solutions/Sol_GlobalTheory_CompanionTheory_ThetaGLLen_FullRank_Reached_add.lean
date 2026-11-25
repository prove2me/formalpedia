-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.Reached.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:04:29.808412+00:00
-- url     : https://prove2.me/submissions/33629c44-2bf0-4223-a4a8-266acbb19a47

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_IsLevel_inf
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_indicator_orb
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_span_le_of_level

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
namespace Reached
theorem _root_.solution {ρ : Representation ℂ H (SB X)}
    (hρ : ∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x))
    (hopen : ∀ x : X, IsOpenMap fun g : H => g • x) {K : Subgroup H} (hK : IsCompact (K : Set H)) {x₀ : X}
    {f f' : SB X} (h : Reached ρ K x₀ f) (h' : Reached ρ K x₀ f') :
    ∃ N : Subgroup H, IsLevel K N ∧ ∃ v : SB X, (∀ x, v.1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) x) ∧
      f ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v) ∧ f' ∈ Submodule.span ℂ (Set.range fun g : H => ρ g v) := by
  obtain ⟨N, hN, v, hv, hf⟩ := h
  obtain ⟨N', hN', v', hv', hf'⟩ := h'
  obtain ⟨u, hu⟩ := exists_indicator_orb hopen hK (hN.inf hN') x₀
  exact ⟨_, hN.inf hN', u, hu, span_le_of_level ρ hρ hK hN (hN.inf hN') inf_le_left x₀ hv hu hf,
    span_le_of_level ρ hρ hK hN' (hN.inf hN') inf_le_right x₀ hv' hu hf'⟩
end Reached
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
