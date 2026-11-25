-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.BiEquivariantSigmaInvariant.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:15:38.163459+00:00
-- url     : https://prove2.me/submissions/042c9180-9924-4842-aa10-c156ac4f65dc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_map_inv_of_antiHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.Automorphic.Whittaker
namespace BiEquivariantSigmaInvariant
theorem _root_.solution {H : Subgroup G} {χ : H → ℂ} {σ : G ≃ₜ G}
    (hσ : ∀ x y, σ (x * y) = σ y * σ x) (h : BiEquivariantSigmaInvariant H χ σ) :
    BiEquivariantSigmaInvariant H (fun g => (χ g)⁻¹) σ := by
  intro D hD f
  set ι : G ≃ₜ G := Homeomorph.inv G
  set D' : Module.Dual ℂ (locallyConstantCompactSupport G ℂ ℂ) := D ∘ₗ compHomeoL ι
  have hD' : ∀ (f : locallyConstantCompactSupport G ℂ ℂ) (h₁ h₂ : H),
      D' (biTranslL (h₁ : G) (h₂ : G) f) = χ h₁ * (χ h₂)⁻¹ * D' f := by
    intro f h₁ h₂
    have e : compHomeoL ι (biTranslL (h₁ : G) (h₂ : G) f) =
        biTranslL (h₂ : G) (h₁ : G) (compHomeoL ι f) :=
      Subtype.ext (funext fun x => by simp [ι, mul_assoc])
    simp only [D', LinearMap.comp_apply, e, hD]
    rw [inv_inv]
    ring
  have key := h D' hD'
  have e : compHomeoL ι (compHomeoL σ f) = compHomeoL σ (compHomeoL ι f) :=
    Subtype.ext (funext fun x => by simp [ι, map_inv_of_antiHom σ hσ])
  have hιι : ∀ g : locallyConstantCompactSupport G ℂ ℂ, compHomeoL ι (compHomeoL ι g) = g :=
    fun g => Subtype.ext (funext fun x => by simp [ι])
  calc D (compHomeoL σ f) = D' (compHomeoL ι (compHomeoL σ f)) := by
        simp only [D', LinearMap.comp_apply, hιι]
    _ = D' (compHomeoL σ (compHomeoL ι f)) := by rw [e]
    _ = D' (compHomeoL ι f) := key _
    _ = D f := by simp only [D', LinearMap.comp_apply, hιι]
end BiEquivariantSigmaInvariant
end GroundTheory.Automorphic.Whittaker
