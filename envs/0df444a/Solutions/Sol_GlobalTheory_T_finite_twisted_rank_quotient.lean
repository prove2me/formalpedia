-- Prove2me | solution 1 for GlobalTheory.T.finite_twisted_rank_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:17:48.564612+00:00
-- url     : https://prove2.me/submissions/05c557d6-328a-4443-a015-a13989dab429

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotientStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_finite_coinv_rightRep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] (κ : ℕ), κ = Fintype.card c → ∀ θ : GL a k →* ℂˣ, Module.Finite ℂ (SB (RankIn k a c {κ}) ⧸ twRel (rightRep (k := k) a c κ) θ) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_rightRep | exact GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_rightRep | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_rightRep <;> assumption)
end _root_.GlobalTheory.T
