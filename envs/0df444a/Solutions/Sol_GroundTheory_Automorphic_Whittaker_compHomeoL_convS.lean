-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.compHomeoL_convS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:23:59.102592+00:00
-- url     : https://prove2.me/submissions/edd52925-ed4e-48bd-9bad-9eb650860288

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [μ.IsHaarMeasure]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [μ.IsMulLeftInvariant] [μ.IsInvInvariant] (σ : G ≃ₜ G)
    (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσμ : μ.map σ = μ)
    (f₁ f₂ : locallyConstantCompactSupport G ℂ ℂ) :
    compHomeoL σ (convS μ f₁ f₂) = convS μ (compHomeoL σ f₂) (compHomeoL σ f₁) := by
  refine Subtype.ext (funext fun x => ?_)
  change groupConv μ f₁ f₂ (σ x) = groupConv μ ((f₂ : G → ℂ) ∘ σ) ((f₁ : G → ℂ) ∘ σ) x
  simp only [groupConv, Function.comp_apply]
  have eR : ∫ y, (f₂ : G → ℂ) (σ y) * (f₁ : G → ℂ) (σ (y⁻¹ * x)) ∂μ =
      ∫ z, (f₂ : G → ℂ) z * (f₁ : G → ℂ) (σ x * z⁻¹) ∂μ := by
    have h := integral_map_equiv (μ := μ) σ.toMeasurableEquiv
      (fun z => (f₂ : G → ℂ) z * (f₁ : G → ℂ) (σ x * z⁻¹))
    simp only [Homeomorph.toMeasurableEquiv_coe, hσμ] at h
    rw [h]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hσ, map_inv_of_antiHom σ hσ]
  have eL : ∫ y, (f₁ : G → ℂ) y * (f₂ : G → ℂ) (y⁻¹ * σ x) ∂μ =
      ∫ z, (f₂ : G → ℂ) z * (f₁ : G → ℂ) (σ x * z⁻¹) ∂μ := by
    rw [← integral_inv_eq_self (fun z => (f₂ : G → ℂ) z * (f₁ : G → ℂ) (σ x * z⁻¹)) μ,
      ← integral_mul_left_eq_self (fun y => (f₁ : G → ℂ) y * (f₂ : G → ℂ) (y⁻¹ * σ x)) (σ x)]
    congr 1
    funext y
    simp only [inv_inv, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    ring
  rw [eL, eR]
end GroundTheory.Automorphic.Whittaker
