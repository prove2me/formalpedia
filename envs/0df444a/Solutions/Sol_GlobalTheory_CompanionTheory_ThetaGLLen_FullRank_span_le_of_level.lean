-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.span_le_of_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:38.212833+00:00
-- url     : https://prove2.me/submissions/2c2e8167-31c1-43c4-b0b7-1337d9ccea25

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_span_translates_le
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_orb_smul_mem_iff
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
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution (ρ : Representation ℂ H (SB X))
    (hρ : ∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x)) {K N N' : Subgroup H}
    (hK : IsCompact (K : Set H)) (hN : IsLevel K N) (hN' : IsLevel K N') (hle : N' ≤ N) (x₀ : X) {v v' : SB X}
    (hv : ∀ x, v.1 x = (orb N x₀).indicator (fun _ => (1 : ℂ)) x)
    (hv' : ∀ x, v'.1 x = (orb N' x₀).indicator (fun _ => (1 : ℂ)) x) :
    Submodule.span ℂ (Set.range fun g : H => ρ g v) ≤ Submodule.span ℂ (Set.range fun g : H => ρ g v') := by
  classical
  refine span_translates_le ρ (mem_span_translates_of_level H X ρ hρ K N' hK hN'.1 hN'.2.1 hN'.2.2 x₀ v' v hv' (fun n hn x => ?_) fun x hx => ?_)
  · rw [hv, hv]
    simp only [Set.indicator, orb_smul_mem_iff (hle hn)]
  · rw [hv] at hx
    have : x ∈ orb N x₀ := by
      by_contra h
      exact hx (Set.indicator_of_notMem h _)
    obtain ⟨n, hn, e⟩ := this
    exact ⟨n, hN.2.1 hn, e⟩
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
