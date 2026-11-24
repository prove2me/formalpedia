-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.orbSum_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:59:02.877953+00:00
-- url     : https://prove2.me/submissions/bc0d11fe-d3cd-4943-80e3-c95d62fb7ca8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_orbSum_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
variable {O : Type} [CommRing O] {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution (φ : A ≃ₐ[O] A') (G : Subgroup Aˣ) (G' : Subgroup A'ˣ)
    (hG : ∀ t : Aˣ, t ∈ G ↔ Units.mapEquiv φ.toMulEquiv t ∈ G')
    (X : Set (Submodule O A)) (X' : Set (Submodule O A'))
    (hX : ∀ L, L ∈ X ↔ L.map φ.toLinearEquiv.toLinearMap ∈ X') :
    orbSum O G' X' (fun _ => 1) = orbSum O G X (fun _ => 1) := by
  rw [orbSum_eq, orbSum_eq]
  set ψ := Units.mapEquiv φ.toMulEquiv with hψ
  have hv : ∀ t : Aˣ, ((ψ t : A'ˣ) : A') = φ t := fun t => rfl
  have hm : ∀ (L : Submodule O A) (y : A), φ y ∈ L.map φ.toLinearEquiv.toLinearMap ↔ y ∈ L := by
    intro L y
    rw [Submodule.mem_map_equiv]
    simp
  let e : X ≃ X' := (Submodule.orderIsoMapComap φ.toLinearEquiv).toEquiv.subtypeEquiv hX
  have he : ∀ L : X, (e L).1 = L.1.map φ.toLinearEquiv.toLinearMap := fun L => rfl
  have hml : ∀ (t : Aˣ) (L : Submodule O A), (mulLat O (t : A) L).map φ.toLinearEquiv.toLinearMap =
      mulLat O ((ψ t : A'ˣ) : A') (L.map φ.toLinearEquiv.toLinearMap) := by
    intro t L
    ext y
    obtain ⟨y, rfl⟩ := φ.surjective y
    rw [hm, mem_mulLat, mem_mulLat, ← map_inv, hv, ← map_mul, hm]
  let q : Orb O G X ≃ Orb O G' X' := Quot.congr e (by
    intro L M
    constructor
    · rintro ⟨t, ht, h⟩
      exact ⟨ψ t, (hG t).1 ht, by rw [he, he, h, hml]⟩
    · rintro ⟨t, ht, h⟩
      obtain ⟨t, rfl⟩ := ψ.surjective t
      refine ⟨t, (hG t).2 ht, ?_⟩
      rw [he, he, ← hml] at h
      exact Submodule.map_injective_of_injective φ.injective h)
  rw [← finsum_comp_equiv q]
  refine finsum_congr fun o => ?_
  induction o using Quot.ind with
  | mk L =>
    change (((stabLat O (e L).1 ⊓ G').relIndex (intUnits O A' ⊓ G') : ℕ) : ℚ) =
      (((stabLat O L.1 ⊓ G).relIndex (intUnits O A ⊓ G) : ℕ) : ℚ)
    have h1 : stabLat O L.1 ⊓ G = (stabLat O (e L).1 ⊓ G').comap ψ.toMonoidHom := by
      ext t
      rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf, hG]
      refine and_congr_left' ?_
      change (∀ y, y ∈ L.1 ↔ (t : A) * y ∈ L.1) ↔ ∀ y, y ∈ (e L).1 ↔ φ t * y ∈ (e L).1
      rw [φ.surjective.forall]
      simp only [he, ← map_mul, hm]
    have h2 : intUnits O A ⊓ G = (intUnits O A' ⊓ G').comap ψ.toMonoidHom := by
      ext t
      rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf, hG]
      refine and_congr_left' ?_
      change (IsIntegral O (t : A) ∧ IsIntegral O ((t⁻¹ : Aˣ) : A)) ↔
        (IsIntegral O (φ t) ∧ IsIntegral O (φ ((t⁻¹ : Aˣ) : A)))
      simp only [isIntegral_algEquiv]
    rw [h1, h2, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective]
end GlobalTheory.UnitLemma.Orbit
