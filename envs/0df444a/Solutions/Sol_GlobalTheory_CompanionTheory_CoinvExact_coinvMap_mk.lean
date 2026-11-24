-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CoinvExact.coinvMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:31.876554+00:00
-- url     : https://prove2.me/submissions/da1294b9-3210-4fd1-b439-cd141c338b9d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExact

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
variable {Γ G V₁ V₂ : Type} [Group Γ] [Group G] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {τ₁ : Representation ℂ (Γ × G) V₁} {τ₂ : Representation ℂ (Γ × G) V₂}
namespace GlobalTheory.CompanionTheory.CoinvExact
theorem _root_.solution (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) (v : V₁) :
    coinvMap φ ψ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (φ v) := rfl
end GlobalTheory.CompanionTheory.CoinvExact
