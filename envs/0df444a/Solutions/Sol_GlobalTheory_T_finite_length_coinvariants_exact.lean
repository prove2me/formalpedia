-- Prove2me | solution 1 for GlobalTheory.T.finite_length_coinvariants_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:15.605649+00:00
-- url     : https://prove2.me/submissions/3b217bcb-1641-4c33-b662-1c29753718d3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExact
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExactStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CoinvExact_main
import Theorems.Thm_GlobalTheory_PowerTwoNormLowerBound_main


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
theorem _root_.solution : ∀ (Γ G W V U : Type) [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (τW : Representation ℂ (Γ × G) W) (τ : Representation ℂ (Γ × G) V) (τU : Representation ℂ (Γ × G) U) (i : τW.IntertwiningMap τ) (f : τ.IntertwiningMap τU), Function.Surjective f → Function.Exact i f → ∀ ψ : Γ →* ℂˣ, HasFiniteLength (coinv τW ψ) → HasFiniteLength (coinv τU ψ) → HasFiniteLength (coinv τ ψ) := by
  first | exact @GlobalTheory.CompanionTheory.CoinvExact.main | exact GlobalTheory.CompanionTheory.CoinvExact.main | (intros; apply GlobalTheory.CompanionTheory.CoinvExact.main <;> assumption)
end _root_.GlobalTheory.T
