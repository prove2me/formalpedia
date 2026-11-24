-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CoinvExact.twRel_le_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:34.284621+00:00
-- url     : https://prove2.me/submissions/12cd47b8-f7e1-4f0d-8ac5-c0db16cba6ab

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExact
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


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
    twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ ≤
      (twRel (τ₁.comp (MonoidHom.inl Γ G)) ψ).map φ.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨γ, u, rfl⟩
  obtain ⟨v, rfl⟩ := hφ u
  refine ⟨τ₁ (γ, 1) v - (ψ γ : ℂ) • v, Submodule.subset_span ⟨γ, v, rfl⟩, ?_⟩
  have e : φ (τ₁ (γ, 1) v) = τ₂ (γ, 1) (φ v) := φ.isIntertwining _ _ _ _
  show φ (τ₁ (γ, 1) v - (ψ γ : ℂ) • v) = τ₂ (γ, 1) (φ v) - (ψ γ : ℂ) • φ v
  rw [map_sub, e, map_smul]
end GlobalTheory.CompanionTheory.CoinvExact
