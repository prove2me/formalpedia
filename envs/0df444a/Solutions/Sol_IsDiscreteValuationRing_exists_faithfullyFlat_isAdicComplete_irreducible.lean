-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_faithfullyFlat_isAdicComplete_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6c138f6d-8111-5bfb-863e-f370088b35fe

import Mathlib
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_faithfullyFlat_isAdicComplete_irreducible

set_option autoImplicit false

universe u

open IsLocalRing IsDedekindDomain

namespace S17B1

theorem charZero_of_irreducible_natCast
    {R : Type u} [CommRing R] [IsDomain R] {p : ℕ} (hunif : Irreducible (p : R)) : CharZero R := by
  classical
  obtain ⟨ℓ, hℓ⟩ := CharP.exists R
  haveI := hℓ
  rcases CharP.char_is_prime_or_zero R ℓ with hprime | hzero
  · exfalso
    by_cases hdvd : ℓ ∣ p
    · have h0 : ((p : ℕ) : R) = 0 := (CharP.cast_eq_zero_iff R ℓ p).mpr hdvd
      rw [h0] at hunif
      exact not_irreducible_zero hunif
    · haveI : Fact ℓ.Prime := ⟨hprime⟩
      have hne : ((p : ℕ) : ZMod ℓ) ≠ 0 := by
        intro h
        rw [ZMod.natCast_eq_zero_iff] at h
        exact hdvd h
      have hu : IsUnit ((p : ℕ) : ZMod ℓ) := Ne.isUnit hne
      have hu' := hu.map (ZMod.castHom (dvd_refl ℓ) R)
      rw [map_natCast] at hu'
      exact hunif.not_isUnit hu'
  · subst hzero
    exact CharP.charP_to_charZero R

theorem le_exp_neg_one_of_lt_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1) := by
  induction γ using WithZero.recZeroCoe with
  | zero => exact bot_le
  | coe m =>
      have hm : (m : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd m) := rfl
      rw [hm] at h ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
      rw [WithZero.exp_le_exp]
      omega

end S17B1

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (p : ℕ) (hunif : Irreducible (p : R)) :
    ∃ (R₁ : Type u) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsDiscreteValuationRing R₁) (_ : CharZero R₁)
      (_ : Algebra R R₁) (_ : Module.FaithfullyFlat R R₁),
      IsAdicComplete (IsLocalRing.maximalIdeal R₁) R₁ ∧ Irreducible (p : R₁) := by
  classical
  haveI : CharZero R := S17B1.charZero_of_irreducible_natCast hunif

  let K := FractionRing R
  let v : HeightOneSpectrum R := ⟨maximalIdeal R, inferInstance, IsDiscreteValuationRing.not_a_field R⟩
  let R₁ := ↥(v.adicCompletionIntegers K)
  have hp0 : (p : R) ≠ 0 := hunif.ne_zero
  have hmax : v.asIdeal = Ideal.span {(p : R)} := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hunif

  have hvalp : Valued.v ((algebraMap R R₁ (p : R) : R₁) : v.adicCompletion K) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_singleton hp0 hmax

  have hvalr : ∀ r : R, Valued.v ((algebraMap R R₁ r : R₁) : v.adicCompletion K) = v.intValuation r := by
    intro r
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap]

  haveI hloc : IsLocalHom (algebraMap R R₁) := by
    refine ⟨fun r hr => ?_⟩
    by_contra hnu
    have hmem : r ∈ v.asIdeal := (mem_maximalIdeal r).mpr (mem_nonunits_iff.mpr hnu)
    have hlt : v.intValuation r < 1 := (v.intValuation_lt_one_iff_mem r).mpr hmem
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, hvalr] at hr
    exact (ne_of_lt hlt) hr
  haveI : Module.Flat R R₁ := inferInstance
  haveI hff : Module.FaithfullyFlat R R₁ := Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI : CharZero R₁ := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective R R₁)

  have hπ0 : ((algebraMap R R₁ (p : R) : R₁) : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvalp
    exact WithZero.zero_ne_coe hvalp
  have hmax₁ : maximalIdeal R₁ = Ideal.span {algebraMap R R₁ (p : R)} := by
    apply le_antisymm
    · intro x hx
      have hxlt : Valued.v (x : v.adicCompletion K) < 1 := by
        have hx' : ¬ IsUnit x := (mem_maximalIdeal x).mp hx
        rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hx'
        exact lt_of_le_of_ne x.2 hx'
      have hxle : Valued.v (x : v.adicCompletion K) ≤ WithZero.exp (-1) := S17B1.le_exp_neg_one_of_lt_one hxlt

      have hq : (x : v.adicCompletion K) / ((algebraMap R R₁ (p : R) : R₁) : v.adicCompletion K)
          ∈ v.adicCompletionIntegers K := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hvalp]
        exact (div_le_one₀ (WithZero.zero_lt_coe _)).mpr hxle
      refine Ideal.mem_span_singleton'.mpr ⟨⟨_, hq⟩, ?_⟩
      apply Subtype.ext
      show ((x : v.adicCompletion K) / ((algebraMap R R₁ (p : R) : R₁) : v.adicCompletion K))
        * ((algebraMap R R₁ (p : R) : R₁) : v.adicCompletion K) = (x : v.adicCompletion K)
      exact div_mul_cancel₀ _ hπ0
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      apply (mem_maximalIdeal _).mpr
      intro hu
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, hvalp] at hu
      exact absurd hu (by decide)
  have hirr₁ : Irreducible (p : R₁) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, hmax₁, map_natCast]
  haveI hcomplete : IsAdicComplete (maximalIdeal R₁) R₁ :=
    HeightOneSpectrum.isAdicComplete_adicCompletionIntegers K v
  exact ⟨R₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hff, hcomplete, hirr₁⟩

end S_IsDiscreteValuationRing_exists_faithfullyFlat_isAdicComplete_irreducible
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_faithfullyFlat_isAdicComplete_irreducible (solution)
