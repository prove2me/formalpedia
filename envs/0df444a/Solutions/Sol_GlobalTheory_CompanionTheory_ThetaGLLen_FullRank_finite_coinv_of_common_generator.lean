-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.finite_coinv_of_common_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:25.151802+00:00
-- url     : https://prove2.me/submissions/eab0bd79-a724-49f4-af89-d696f4adf0d1

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
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution : ∀ (H V : Type) [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (θ : H →* ℂˣ), (∀ w w' : V, ∃ t : V, w ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t) ∧ w' ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t)) → Module.Finite ℂ (V ⧸ twRel ρ θ) := by
  intro H V _ _ _ ρ θ h
  have hq : ∀ (g : H) (t : V), (twRel ρ θ).mkQ (ρ g t) = (θ g : ℂ) • (twRel ρ θ).mkQ t := by
    intro g t
    rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨g, t, rfl⟩
  have hspan : ∀ t w : V, w ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t) →
      ∃ s : ℂ, (twRel ρ θ).mkQ w = s • (twRel ρ θ).mkQ t := by
    intro t w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨θ g, hq g t⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs⟩ := hx
      obtain ⟨u, hu⟩ := hy
      exact ⟨s + u, by rw [map_add, hs, hu, add_smul]⟩
    | smul c x _ hx =>
      obtain ⟨s, hs⟩ := hx
      exact ⟨c * s, by rw [map_smul, hs, mul_smul]⟩
  by_cases h0 : ∀ w : V, (twRel ρ θ).mkQ w = 0
  · haveI : Subsingleton (V ⧸ twRel ρ θ) := ⟨fun p q => by
      obtain ⟨w, rfl⟩ := (twRel ρ θ).mkQ_surjective p
      obtain ⟨w', rfl⟩ := (twRel ρ θ).mkQ_surjective q
      rw [h0, h0]⟩
    infer_instance
  · push Not at h0
    obtain ⟨w₀, hw₀⟩ := h0
    refine ⟨⟨{(twRel ρ θ).mkQ w₀}, ?_⟩⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨w, rfl⟩ := (twRel ρ θ).mkQ_surjective z
    obtain ⟨t, ht, ht'⟩ := h w w₀
    obtain ⟨s, hs⟩ := hspan t w ht
    obtain ⟨s₀, hs₀⟩ := hspan t w₀ ht'
    have hne : s₀ ≠ 0 := fun e => hw₀ (by rw [hs₀, e, zero_smul])
    have : (twRel ρ θ).mkQ w = (s / s₀) • (twRel ρ θ).mkQ w₀ := by
      rw [hs, hs₀, smul_smul, div_mul_cancel₀ _ hne]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
