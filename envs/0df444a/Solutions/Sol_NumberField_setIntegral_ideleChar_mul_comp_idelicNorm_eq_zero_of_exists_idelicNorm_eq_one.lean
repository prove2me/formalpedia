-- Prove2me | solution 1 for NumberField.setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cdf53eb7-3145-54c5-a268-82e6f3f11dc6

import Mathlib.LinearAlgebra.Countable
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one

set_option autoImplicit false

open MeasureTheory NumberField
open scoped Pointwise

namespace R2FafNB

theorem adelicNorm_algebraMap_algEquiv
    {R E S F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E] [IsFractionRing R E]
    [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F] [IsFractionRing S F] [Algebra E F]
    (B : M4aHerbrand.AdeleBaseChange R E S F) (σ : F ≃ₐ[E] F) (x : F) :
    B.adelicNorm (algebraMap F (AdeleRing S F) (σ x)) =
      B.adelicNorm (algebraMap F (AdeleRing S F) x) := by
  letI := B.β.toAlgebra
  have h := M4aHerbrand.actOf_algebraMap R E S F B.tensorEquiv B.tensorEquiv_one_tmul σ x
  rw [← h]
  exact Algebra.norm_eq_of_algEquiv
    (B.tensorEquiv.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl σ).trans B.tensorEquiv))
    (algebraMap F (AdeleRing S F) x)

theorem idelicNorm_unitsMap_div_eq_one
    {R E S F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E] [IsFractionRing R E]
    [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F] [IsFractionRing S F] [Algebra E F]
    (B : M4aHerbrand.AdeleBaseChange R E S F) (σ : F ≃ₐ[E] F) (w : Fˣ) :
    B.idelicNorm ((Units.map (algebraMap F (AdeleRing S F) : F →* AdeleRing S F))
      ((Units.map ((σ : F →+* F) : F →* F) / MonoidHom.id Fˣ) w)) = 1 := by
  rw [MonoidHom.div_apply, MonoidHom.id_apply, map_div, map_div, div_eq_one]
  ext
  simp only [M4aHerbrand.AdeleBaseChange.idelicNorm, Units.coe_map, MonoidHom.coe_coe]
  exact adelicNorm_algebraMap_algEquiv B σ (w : F)

theorem countable_units (F : Type*) [Field F] [NumberField F] : Countable Fˣ := by
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  exact Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective

theorem countable_range {G H : Type*} [Group G] [Group H] [Countable G] (φ : G →* H) :
    Countable φ.range :=
  Function.Surjective.countable (MonoidHom.rangeRestrict_surjective φ)

end R2FafNB

open R2FafNB in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (hker : ∃ t : (AdeleRing (𝓞 L) L)ˣ,
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm t = 1 ∧ ξ ⟨t, Subgroup.mem_top t⟩ ≠ 1)
    (g : (AdeleRing (𝓞 K) K)ˣ → ℂ) (hg : Measurable g) :
    ∫ z in Θ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL = 0 := by
  classical

  set N := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hN
  set ιL : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
    Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) with hιL
  set Δ : Subgroup (AdeleRing (𝓞 L) L)ˣ :=
    (ιL.comp (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range with hΔ
  set f : (AdeleRing (𝓞 L) L)ˣ → ℂ :=
    fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * g (N z) with hf
  obtain ⟨t, hNt, hξt1⟩ := hker

  have hξmul : ∀ a b : (AdeleRing (𝓞 L) L)ˣ,
      ξ ⟨a * b, Subgroup.mem_top _⟩ = ξ ⟨a, Subgroup.mem_top a⟩ * ξ ⟨b, Subgroup.mem_top b⟩ :=
    fun a b => by rw [← map_mul]; rfl

  have hΔprin : ∀ δ : Δ, ((δ : (AdeleRing (𝓞 L) L)ˣ)) ∈ ιL.range := by
    rintro ⟨_, w, rfl⟩
    exact ⟨_, rfl⟩

  have hΔnorm : ∀ δ : Δ, N (δ : (AdeleRing (𝓞 L) L)ˣ) = 1 := by
    rintro ⟨_, w, rfl⟩
    exact idelicNorm_unitsMap_div_eq_one _ σ w

  have hfinv : ∀ (δ : Δ) (z : (AdeleRing (𝓞 L) L)ˣ), f (δ • z) = f z := by
    intro δ z
    rw [Subgroup.smul_def, smul_eq_mul]
    simp only [hf, hξmul, hξt _ (hΔprin δ), one_mul, map_mul, hΔnorm]

  haveI : Countable Lˣ := countable_units L
  haveI : Countable Δ := countable_range _

  have h1 : ∫ z in Θ, f z ∂νZL = ∫ z in t • Θ, f z ∂νZL :=
    hΘ.setIntegral_eq (hΘ.smul_of_comm t) hfinv

  have h2 : ∫ z in t • Θ, f z ∂νZL = ∫ z in Θ, f (t • z) ∂νZL := by
    rw [← Set.image_smul]
    exact (measurePreserving_smul t νZL).setIntegral_image_emb (measurableEmbedding_const_smul t) f Θ

  have h3 : ∀ z, f (t • z) = ((ξ ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ) * f z := by
    intro z
    simp only [hf, smul_eq_mul, hξmul, map_mul, hNt, one_mul, Units.val_mul, mul_assoc]
  have h4 : ∫ z in Θ, f (t • z) ∂νZL =
      ((ξ ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ) * ∫ z in Θ, f z ∂νZL := by
    simp_rw [h3]
    exact integral_const_mul _ _

  have hne : ((ξ ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ) ≠ 1 := fun h => hξt1 (Units.ext h)
  have key : (1 - ((ξ ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ)) * ∫ z in Θ, f z ∂νZL = 0 := by
    rw [sub_mul, one_mul, ← h4, ← h2, ← h1, sub_self]
  rcases mul_eq_zero.1 key with h | h
  · exact absurd (sub_eq_zero.1 h).symm hne
  · exact h

end S_NumberField_setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one
end P2MW
export P2MW.S_NumberField_setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one (solution)
