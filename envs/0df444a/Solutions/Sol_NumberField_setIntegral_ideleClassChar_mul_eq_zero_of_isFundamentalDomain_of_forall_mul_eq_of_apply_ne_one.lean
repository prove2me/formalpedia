-- Prove2me | solution 1 for NumberField.setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/848ab0e7-3dd7-5437-9bda-e70bad203d18

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Group.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one

set_option autoImplicit false

open MeasureTheory NumberField

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξKt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (t : (AdeleRing (𝓞 K) K)ˣ) (ht : ξK ⟨t, Subgroup.mem_top t⟩ ≠ 1)
    (F : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hFK : ∀ γ : (AdeleRing (𝓞 K) K)ˣ,
      γ ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ∀ z : (AdeleRing (𝓞 K) K)ˣ, F (γ * z) = F z)
    (hFt : ∀ z : (AdeleRing (𝓞 K) K)ˣ, F (z * t) = F z) :
    ∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * F z ∂νZK = 0 := by
  classical
  set Γ := (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range with hΓ

  set f : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun z => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * F z with hf
  have hfΓ : ∀ (γ : Γ) (z : (AdeleRing (𝓞 K) K)ˣ), f (γ • z) = f z := by
    intro γ z
    show f ((γ : (AdeleRing (𝓞 K) K)ˣ) * z) = f z
    simp only [f]
    have hmul : (⟨(γ : (AdeleRing (𝓞 K) K)ˣ) * z, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) =
        ⟨(γ : (AdeleRing (𝓞 K) K)ˣ), Subgroup.mem_top _⟩ * ⟨z, Subgroup.mem_top z⟩ := rfl
    rw [hmul, map_mul, hξKt _ γ.2, one_mul, hFK _ γ.2]

  haveI : Countable K := by
    let b := Module.finBasis ℚ K
    exact Function.Surjective.countable b.equivFun.symm.surjective
  haveI : Countable Kˣ := Function.Injective.countable (Units.val_injective (α := K))
  haveI : Countable Γ := Function.Surjective.countable (MonoidHom.rangeRestrict_surjective _)
  haveI : MeasurableConstSMul Γ (AdeleRing (𝓞 K) K)ˣ :=
    ⟨fun γ => (continuous_mul_left (γ : (AdeleRing (𝓞 K) K)ˣ)).measurable⟩
  haveI : SMulInvariantMeasure Γ (AdeleRing (𝓞 K) K)ˣ νZK :=
    ⟨fun γ s hs => (measurePreserving_mul_left νZK (γ : (AdeleRing (𝓞 K) K)ˣ)).measure_preimage
      hs.nullMeasurableSet⟩

  have hΩ' : IsFundamentalDomain Γ ((fun z : (AdeleRing (𝓞 K) K)ˣ => t * z) ⁻¹' ΩK) νZK :=
    hΩK.preimage_of_equiv (measurePreserving_mul_left νZK t).quasiMeasurePreserving
      Function.bijective_id (fun γ z => by
        show t * ((γ : (AdeleRing (𝓞 K) K)ˣ) * z) = (γ : (AdeleRing (𝓞 K) K)ˣ) * (t * z)
        rw [mul_left_comm])
  have h1 : ∫ z in ΩK, f z ∂νZK = ∫ z in (fun z : (AdeleRing (𝓞 K) K)ˣ => t * z) ⁻¹' ΩK, f z ∂νZK :=
    hΩK.setIntegral_eq hΩ' hfΓ

  have h2 : ∫ z in (fun z : (AdeleRing (𝓞 K) K)ˣ => t * z) ⁻¹' ΩK, f z ∂νZK =
      ∫ y in ΩK, f (t⁻¹ * y) ∂νZK := by
    have := (measurePreserving_mul_left νZK t).setIntegral_preimage_emb
      (MeasurableEquiv.mulLeft t).measurableEmbedding (fun y => f (t⁻¹ * y)) ΩK
    simpa only [inv_mul_cancel_left] using this

  have h3 : ∀ y : (AdeleRing (𝓞 K) K)ˣ, f (t⁻¹ * y) = ((ξK ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ)⁻¹ * f y := by
    intro y
    simp only [f]
    have hmul : (⟨t⁻¹ * y, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) =
        ⟨t, Subgroup.mem_top t⟩⁻¹ * ⟨y, Subgroup.mem_top y⟩ := rfl
    have hF : F (t⁻¹ * y) = F y := by
      have := hFt (t⁻¹ * y)
      rw [mul_comm t⁻¹ y, mul_assoc, inv_mul_cancel, mul_one] at this
      rw [mul_comm t⁻¹ y]
      exact this.symm
    rw [hmul, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hF, mul_assoc]

  have h4 : ∫ y in ΩK, f (t⁻¹ * y) ∂νZK =
      ((ξK ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ)⁻¹ * ∫ y in ΩK, f y ∂νZK := by
    simp_rw [h3]
    exact integral_const_mul _ _
  have hI : ∫ z in ΩK, f z ∂νZK = ((ξK ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ)⁻¹ * ∫ z in ΩK, f z ∂νZK := by
    rw [← h4, ← h2, ← h1]
  have hc1 : ((ξK ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ)⁻¹ ≠ 1 := by
    intro h
    apply ht
    apply Units.ext
    have := inv_eq_one.mp h
    simpa using this
  have hfin : (1 - ((ξK ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ)⁻¹) * ∫ z in ΩK, f z ∂νZK = 0 := by
    rw [sub_mul, one_mul, ← hI, sub_self]
  rcases mul_eq_zero.mp hfin with h | h
  · exact absurd (sub_eq_zero.mp h).symm hc1
  · simpa only [f] using h

end S_NumberField_setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one
end P2MW
export P2MW.S_NumberField_setIntegral_ideleClassChar_mul_eq_zero_of_isFundamentalDomain_of_forall_mul_eq_of_apply_ne_one (solution)
