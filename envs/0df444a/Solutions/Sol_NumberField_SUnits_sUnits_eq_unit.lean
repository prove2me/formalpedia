-- Prove2me | solution 1 for NumberField.SUnits.sUnits_eq_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e4ae3c1f-023f-57ef-bdc9-abb0ae077099

import Mathlib
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_sUnits_eq_unit

set_option autoImplicit false

namespace P2mS26SU

open IsDedekindDomain NumberField

lemma eq_of_forall_le_exp_neg_iff {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  obtain ⟨α, rfl⟩ : ∃ α : ℤ, a = WithZero.exp α := ⟨_, (WithZero.exp_log ha).symm⟩
  obtain ⟨β, rfl⟩ : ∃ β : ℤ, b = WithZero.exp β := ⟨_, (WithZero.exp_log hb).symm⟩
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
  simp only [WithZero.exp_le_exp] at h
  have h1 := (h (-α).toNat).1 (by omega)
  have h2 := (h (-β).toNat).2 (by omega)
  congr 1
  omega

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

theorem intValuation_comap (e : R ≃+* R') (v : HeightOneSpectrum R') (r : R) :
    (HeightOneSpectrum.comap e.toRingHom e.surjective v).intValuation r = v.intValuation (e r) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  apply eq_of_forall_le_exp_neg_iff (HeightOneSpectrum.intValuation_ne_zero _ _ hr)
    (HeightOneSpectrum.intValuation_ne_zero _ _ (by simpa using hr)) (HeightOneSpectrum.intValuation_le_one _ _)
    (HeightOneSpectrum.intValuation_le_one _ _)
  intro n
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
    HeightOneSpectrum.comap_asIdeal]
  change r ∈ Ideal.comap e v.asIdeal ^ n ↔ e r ∈ v.asIdeal ^ n
  rw [← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]

end P2mS26SU

namespace P2mS26SU
open IsDedekindDomain NumberField

variable (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]

noncomputable abbrev galInt (σ : K ≃ₐ[E] K) : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv (σ : K ≃+* K)

omit [NumberField K] in
theorem coe_galInt (σ : K ≃ₐ[E] K) (x : 𝓞 K) : ((galInt E K σ x : 𝓞 K) : K) = σ (x : K) :=
  RingOfIntegers.mapRingEquiv_apply _ _

noncomputable def pullback (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) :=
  HeightOneSpectrum.comap (galInt E K σ).toRingHom (galInt E K σ).surjective w

omit [NumberField K] in
theorem galInt_algebraMap (σ : K ≃ₐ[E] K) (e : 𝓞 E) : galInt E K σ (algebraMap (𝓞 E) (𝓞 K) e) = algebraMap (𝓞 E) (𝓞 K) e := by
  apply RingOfIntegers.coe_injective
  change ((galInt E K σ (algebraMap (𝓞 E) (𝓞 K) e) : 𝓞 K) : K) = ((algebraMap (𝓞 E) (𝓞 K) e : 𝓞 K) : K)
  rw [coe_galInt, RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 K) K,
    IsScalarTower.algebraMap_apply (𝓞 E) E K, AlgEquiv.commutes]

omit [NumberField K] in

theorem under_pullback (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    (pullback E K σ w).under (𝓞 E) = w.under (𝓞 E) := by
  apply HeightOneSpectrum.ext
  change Ideal.comap (algebraMap (𝓞 E) (𝓞 K)) (pullback E K σ w).asIdeal = Ideal.comap (algebraMap (𝓞 E) (𝓞 K)) w.asIdeal
  rw [pullback, HeightOneSpectrum.comap_asIdeal, Ideal.comap_comap]
  congr 1
  exact RingHom.ext fun e => galInt_algebraMap E K σ e

theorem valuation_apply_eq_valuation_pullback (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (y : K) :
    w.valuation K (σ y) = (pullback E K σ w).valuation K y := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (𝓞 K)) y
  have hs : (galInt E K σ s : 𝓞 K) ∈ nonZeroDivisors (𝓞 K) :=
    mem_nonZeroDivisors_of_ne_zero (by simp)
  have hσ : σ (IsLocalization.mk' K r s) = IsLocalization.mk' K (galInt E K σ r) ⟨galInt E K σ s, hs⟩ := by
    rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, map_div₀]
    change σ ((r : 𝓞 K) : K) / σ ((s : 𝓞 K) : K) = ((galInt E K σ r : 𝓞 K) : K) / ((galInt E K σ s : 𝓞 K) : K)
    rw [coe_galInt, coe_galInt]
  rw [hσ, HeightOneSpectrum.valuation_of_mk', HeightOneSpectrum.valuation_of_mk', pullback,
    intValuation_comap, intValuation_comap]

end P2mS26SU

theorem solution (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) :
    NumberField.SUnits.sUnits E K S = Set.unit (NumberField.SUnits.placesAbove E K S) K := by
  apply le_antisymm
  · intro x hx w hw
    have := (NumberField.SUnits.mem_sUnits_iff E K S x).1 hx 1 w hw
    simpa using this
  · intro x hx
    rw [NumberField.SUnits.mem_sUnits_iff]
    intro σ w hw
    rw [P2mS26SU.valuation_apply_eq_valuation_pullback E K σ w]
    exact hx (P2mS26SU.pullback E K σ w) (by
      rw [NumberField.SUnits.mem_placesAbove, P2mS26SU.under_pullback]; exact hw)

end S_NumberField_SUnits_sUnits_eq_unit
end P2MW
export P2MW.S_NumberField_SUnits_sUnits_eq_unit (solution)
