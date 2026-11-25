-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CoinvExact.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:27.144795+00:00
-- url     : https://prove2.me/submissions/0d908383-d87a-4f8e-86a8-954cb023b2a9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExact
import Theorems.Thm_GlobalTheory_CompanionTheory_CoinvExact_hasFiniteLength_of_exact
import Theorems.Thm_GlobalTheory_CompanionTheory_CoinvExact_coinvMap_surjective
import Theorems.Thm_GlobalTheory_CompanionTheory_CoinvExact_coinvMap_exact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CoinvExact
namespace GlobalTheory.CompanionTheory.CoinvExact
theorem _root_.solution : ∀ (Γ G W V U : Type) [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (τW : Representation ℂ (Γ × G) W) (τ : Representation ℂ (Γ × G) V) (τU : Representation ℂ (Γ × G) U) (i : τW.IntertwiningMap τ) (f : τ.IntertwiningMap τU), Function.Surjective f → Function.Exact i f → ∀ ψ : Γ →* ℂˣ, HasFiniteLength (coinv τW ψ) → HasFiniteLength (coinv τU ψ) → HasFiniteLength (coinv τ ψ) := by
  intro Γ G W V U _ _ _ _ _ _ _ _ τW τ τU i f hf hif ψ hW hU
  exact hasFiniteLength_of_exact _ _ _ (coinvMap i ψ) (coinvMap f ψ)
    (coinvMap_surjective f hf ψ) (coinvMap_exact i f hf hif ψ) hW hU
end GlobalTheory.CompanionTheory.CoinvExact
