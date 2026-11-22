-- Prove2me | solution 1 for LCAGroup.continuousMonoidHom_dual_equiv
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:49:08.72821+00:00
-- url     : https://prove2.me/submissions/9930c7b3-4baf-4ae8-9e1e-15ee4a7f0084

import Mathlib
import Theorems.Thm_LCAGroup_pontryagin_duality

open Topology

set_option autoImplicit false

theorem solution
    (A G : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] [LocallyCompactSpace A]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    ∃ e : (A →ₜ* G) ≃ₜ* (PontryaginDual G →ₜ* PontryaginDual A),
      ∀ f : A →ₜ* G, e f = PontryaginDual.map f := by
  obtain ⟨αA, hαA⟩ := LCAGroup.pontryagin_duality A
  obtain ⟨αG, hαG⟩ := LCAGroup.pontryagin_duality G
  -- the evaluation isomorphisms as continuous homomorphisms
  let a : A →ₜ* PontryaginDual (PontryaginDual A) :=
    ContinuousMonoidHom.toContinuousMonoidHom αA
  let g' : PontryaginDual (PontryaginDual G) →ₜ* G :=
    ContinuousMonoidHom.toContinuousMonoidHom αG.symm
  -- the candidate inverse: φ ↦ ι_G⁻¹ ∘ φ^ ∘ ι_A
  let ψ : (PontryaginDual G →ₜ* PontryaginDual A) → (A →ₜ* G) := fun φ =>
    (g'.comp (PontryaginDual.map φ)).comp a
  have hψ : ∀ φ x, ψ φ x = αG.symm (PontryaginDual.map φ (αA x)) := fun _ _ => rfl
  -- key identity: χ (ι_G⁻¹ z) = z χ
  have hkey : ∀ (z : PontryaginDual (PontryaginDual G)) (χ : PontryaginDual G),
      χ (αG.symm z) = z χ := by
    intro z χ
    rw [← hαG (αG.symm z) χ, ContinuousMulEquiv.apply_symm_apply]
  have hψc : Continuous ψ := by
    have h1 : Continuous fun φ : PontryaginDual G →ₜ* PontryaginDual A =>
        PontryaginDual.map φ :=
      (PontryaginDual.mapHom (PontryaginDual G) (PontryaginDual A)).continuous
    exact (ContinuousMonoidHom.continuous_comp_left a).comp
      ((ContinuousMonoidHom.continuous_comp_right g').comp h1)
  have hleft : ∀ f : A →ₜ* G, ψ (PontryaginDual.map f) = f := by
    intro f
    ext x
    rw [hψ]
    apply αG.injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    ext χ
    rw [hαG, PontryaginDual.map_apply, hαA, PontryaginDual.map_apply]
  have hright : ∀ φ : PontryaginDual G →ₜ* PontryaginDual A,
      PontryaginDual.map (ψ φ) = φ := by
    intro φ
    ext χ x
    rw [PontryaginDual.map_apply, hψ, hkey, PontryaginDual.map_apply, hαA]
  exact ⟨{ toFun := PontryaginDual.map
           invFun := ψ
           left_inv := hleft
           right_inv := hright
           map_mul' := PontryaginDual.map_mul
           continuous_toFun := (PontryaginDual.mapHom A G).continuous
           continuous_invFun := hψc }, fun _ => rfl⟩
