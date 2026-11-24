-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CoinvExact.coinvMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:44:30.636533+00:00
-- url     : https://prove2.me/submissions/0a314782-e57a-4239-93a8-5552888c02f5

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
theorem _root_.solution (φ : τ₁.IntertwiningMap τ₂) (hφ : Function.Surjective φ) (ψ : Γ →* ℂˣ) :
    Function.Surjective (coinvMap φ ψ) := by
  intro y
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, rfl⟩ := hφ u
  exact ⟨Submodule.Quotient.mk v, rfl⟩
end GlobalTheory.CompanionTheory.CoinvExact
