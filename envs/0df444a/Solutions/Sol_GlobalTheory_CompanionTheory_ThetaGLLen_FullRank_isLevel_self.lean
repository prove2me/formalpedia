-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.isLevel_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:15.488885+00:00
-- url     : https://prove2.me/submissions/7707dfb8-916b-4a63-953f-ae9bb55f3f10

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
variable {H X : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace X] [MulAction H X]
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution {K : Subgroup H} (h : IsOpen (K : Set H)) : IsLevel K K :=
  ⟨h, le_rfl, fun _ hκ _ hn => K.mul_mem (K.mul_mem hκ hn) (K.inv_mem hκ)⟩
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
