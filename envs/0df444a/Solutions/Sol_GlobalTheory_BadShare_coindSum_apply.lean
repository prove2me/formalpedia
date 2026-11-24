-- Prove2me | solution 1 for GlobalTheory.BadShare.coindSum_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:00:13.821797+00:00
-- url     : https://prove2.me/submissions/b144adc7-7d38-48fd-8b10-9458f735f06b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
noncomputable section
open GlobalTheory GlobalTheory.BadShare
variable {G : Type} [Group G] [Fintype G] {Γ : Type} [Group Γ] [Fintype Γ] (r : Γ →* G)
  {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ Γ W)
omit [Fintype G] [FiniteDimensional ℂ W]
namespace GlobalTheory.BadShare
theorem _root_.solution (φ : G → W) (x : G) :
    (coindSum r σ φ).1 x = ∑ γ : Γ, σ γ⁻¹ (φ (r γ * x)) := by
  change (∑ γ : Γ, (σ γ⁻¹ : W →ₗ[ℂ] W).compLeft G ∘ₗ LinearMap.funLeft ℂ W fun x => r γ * x) φ x = _
  simp [LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]
end GlobalTheory.BadShare
