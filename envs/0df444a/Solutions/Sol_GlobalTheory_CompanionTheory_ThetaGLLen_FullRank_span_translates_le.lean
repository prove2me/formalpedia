-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.span_translates_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:45.013687+00:00
-- url     : https://prove2.me/submissions/b7f3aad6-1a7d-4914-a1da-a4c7d19b8684

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_translate_mem_span

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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) {t v : V}
    (hv : v ∈ Submodule.span ℂ (Set.range fun h : H => ρ h t)) :
    Submodule.span ℂ (Set.range fun h : H => ρ h v) ≤ Submodule.span ℂ (Set.range fun h : H => ρ h t) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, rfl⟩
  exact translate_mem_span ρ t h hv
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
