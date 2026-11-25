-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_ne_zero_doubleContragredient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:19:58.676222+00:00
-- url     : https://prove2.me/submissions/9128aabe-406d-4d17-be51-012ef728c963

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_toDoubleContragredient_bijective


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
  [T2Space G] [TotallyDisconnectedSpace G] [TopologicalSpace.SeparableSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {σ : G ≃ₜ G} {H : Subgroup G} {χ : H → ℂ}
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [TopologicalSpace.SeparableSpace G] [MeasurableSpace G] [BorelSpace G]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] (h : IsAdmissible ρ)
    (hne : equivariantFunctionals ρ χ ≠ ⊥) :
    equivariantFunctionals (contragredient (contragredient ρ)) (fun g => ((χ g)⁻¹)⁻¹) ≠ ⊥ := by
  obtain ⟨ℓ, hℓ, hℓ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let Φ := LinearEquiv.ofBijective (toDoubleContragredient h.1).toLinearMap
    (toDoubleContragredient_bijective h)
  have hΦ : ∀ x, Φ x = toDoubleContragredient h.1 x := fun _ => rfl
  let ℓ' : Module.Dual ℂ (smoothVectors (Representation.dual (contragredient ρ))) :=
    ℓ ∘ₗ Φ.symm.toLinearMap
  have hℓ'Φ : ∀ x, ℓ' (Φ x) = ℓ x := fun x => by
    simp only [ℓ', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  intro hbot
  have hmem : ℓ' ∈ equivariantFunctionals (contragredient (contragredient ρ))
      (fun g => ((χ g)⁻¹)⁻¹) := by
    intro g y
    obtain ⟨x, rfl⟩ := Φ.surjective y
    show ℓ' (contragredient (contragredient ρ) g (Φ x)) = ((χ g)⁻¹)⁻¹ * ℓ' (Φ x)
    have e1 : contragredient (contragredient ρ) g (Φ x) = Φ (ρ g x) := by
      rw [hΦ, hΦ, (toDoubleContragredient h.1).isIntertwining]
    rw [inv_inv, e1, hℓ'Φ, hℓ'Φ]
    exact hℓ g x
  rw [hbot] at hmem
  have h0 : ℓ' = 0 := (Submodule.mem_bot ℂ).1 hmem
  apply hℓ0
  refine LinearMap.ext fun x => ?_
  rw [← hℓ'Φ, h0]
  rfl
end GroundTheory.Automorphic.Whittaker
