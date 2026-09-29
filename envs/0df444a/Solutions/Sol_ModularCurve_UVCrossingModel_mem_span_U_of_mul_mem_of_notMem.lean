-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.mem_span_U_of_mul_mem_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/40fe4ded-0687-5f65-9044-6af5fef4a714

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_mem_span_U_of_mul_mem_of_notMem

set_option autoImplicit false
set_option linter.unusedSectionVars false

open ModularCurve ModularCurve.UVCrossingModel

namespace UPrimaryAux

open PowerSeries

theorem mem_nonZeroDivisors_add_of_isNilpotent {R : Type*} [CommRing R] {a ν : R}
    (ha : a ∈ nonZeroDivisors R) (hν : IsNilpotent ν) : a + ν ∈ nonZeroDivisors R := by
  obtain ⟨k, hk⟩ := hν
  rw [mem_nonZeroDivisors_iff_right]
  intro g hg

  have key : ∀ j : ℕ, a ^ j * g = (-ν) ^ j * g := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hag : a * g = -ν * g := by
        have : (a + ν) * g = 0 := by rw [mul_comm]; exact hg
        linear_combination this
      calc a ^ (j + 1) * g = a ^ j * (a * g) := by ring
        _ = a ^ j * (-ν * g) := by rw [hag]
        _ = -ν * (a ^ j * g) := by ring
        _ = -ν * ((-ν) ^ j * g) := by rw [ih]
        _ = (-ν) ^ (j + 1) * g := by ring
  have h0 : a ^ k * g = 0 := by rw [key k, neg_pow, hk, mul_zero, zero_mul]
  rw [mul_comm] at h0
  exact (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem ha k)).mp h0

theorem X_pow_mem_nonZeroDivisors {R : Type*} [CommRing R] (d : ℕ) : (X : R⟦X⟧) ^ d ∈ nonZeroDivisors R⟦X⟧ := by
  apply pow_mem
  rw [mem_nonZeroDivisors_iff_right]
  intro g hg
  ext n
  have := congrArg (coeff (n + 1)) hg
  rwa [mul_comm, coeff_succ_X_mul, map_zero] at this

theorem mem_nonZeroDivisors_of_coeff {R : Type*} [CommRing R] (F : R⟦X⟧) (d : ℕ)
    (hlow : ∀ i < d, IsNilpotent (coeff i F)) (hd : IsUnit (coeff d F)) : F ∈ nonZeroDivisors R⟦X⟧ := by

  have hdvd : (X : R⟦X⟧) ^ d ∣ F - (trunc d F : R⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hi, sub_self]
  obtain ⟨G, hG⟩ := hdvd
  have hF : F = X ^ d * G + (trunc d F : R⟦X⟧) := by rw [← hG]; ring

  have hG0 : constantCoeff G = coeff d F := by
    have := congrArg (coeff d) hG
    rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_neg (lt_irrefl d), sub_zero,
      coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self] at this
    rw [← coeff_zero_eq_constantCoeff_apply, this]
  have hGu : IsUnit G := isUnit_iff_constantCoeff.mpr (hG0 ▸ hd)

  have hnil : IsNilpotent ((trunc d F : Polynomial R) : R⟦X⟧) := by
    have hP : IsNilpotent (trunc d F) := by
      rw [Polynomial.isNilpotent_iff]
      intro i
      rw [coeff_trunc]
      split_ifs with hi
      · exact hlow i hi
      · exact IsNilpotent.zero
    exact hP.map (Polynomial.coeToPowerSeries.ringHom : Polynomial R →+* R⟦X⟧)
  rw [hF]
  apply mem_nonZeroDivisors_add_of_isNilpotent _ hnil
  obtain ⟨u, hu⟩ := hGu
  rw [← hu]
  exact mul_mem (X_pow_mem_nonZeroDivisors d) (Units.isUnit u).mem_nonZeroDivisors

end UPrimaryAux

open UPrimaryAux PowerSeries in
theorem solution
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ϖ : W) (hϖ : Irreducible ϖ) (m : ℕ) (hm : 1 ≤ m)
    (s f : UVCrossingModel W (ϖ ^ m))
    (hs : s ∉ Ideal.span {const (ϖ ^ m) ϖ, U (ϖ ^ m)})
    (h : s * f ∈ Ideal.span {U (ϖ ^ m)}) :
    f ∈ Ideal.span {U (ϖ ^ m)} := by
  classical

  have hϖm : ¬ IsUnit (ϖ ^ m) := by
    rw [isUnit_pow_iff (by omega)]
    exact hϖ.not_isUnit
  haveI : Nontrivial (W ⧸ Ideal.span {ϖ ^ m}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) ϖ) :=
    ⟨m, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_span_singleton_self _⟩
  have hnonunit : ∀ r : W, ¬ IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) r) → ∃ b : W, r = ϖ * b := by
    intro r hr
    have hr' : ¬ IsUnit r := fun hu => hr (hu.map _)
    have hmem : r ∈ IsLocalRing.maximalIdeal W := hr'
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, by rw [← ha, mul_comm]⟩

  obtain ⟨e, -, -, heC⟩ := UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries (ϖ ^ m)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hsf : Ideal.Quotient.mk (Ideal.span {U (ϖ ^ m)}) s * Ideal.Quotient.mk (Ideal.span {U (ϖ ^ m)}) f = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact h
  set F := e (Ideal.Quotient.mk (Ideal.span {U (ϖ ^ m)}) s) with hFdef

  have hex : ∃ i, IsUnit (coeff i F) := by
    by_contra hall
    push Not at hall
    have hcoef : ∀ i, ∃ b : W, coeff i F =
        Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) ϖ * Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) b := by
      intro i
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (coeff i F)
      obtain ⟨b, hb⟩ := hnonunit r (by rw [hr]; exact hall i)
      exact ⟨b, by rw [← hr, hb, map_mul]⟩
    choose b hb using hcoef
    have hF : F = C (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) ϖ) *
        PowerSeries.mk (fun i => Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) (b i)) := by
      ext i
      rw [coeff_C_mul, coeff_mk, hb]
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective
      (e.symm (PowerSeries.mk fun i => Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) (b i)))
    have hqs : Ideal.Quotient.mk (Ideal.span {U (ϖ ^ m)}) s =
        Ideal.Quotient.mk (Ideal.span {U (ϖ ^ m)}) (const (ϖ ^ m) ϖ * g) := by
      apply e.injective
      show F = _
      rw [map_mul, map_mul, heC, hg, RingEquiv.apply_symm_apply, hF]
    apply hs
    have hmem : s - const (ϖ ^ m) ϖ * g ∈ Ideal.span {U (ϖ ^ m)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      exact hqs
    rw [Ideal.mem_span_singleton'] at hmem
    obtain ⟨a, ha⟩ := hmem
    rw [Ideal.mem_span_pair]
    exact ⟨g, a, by linear_combination ha⟩

  have hd : IsUnit (coeff (Nat.find hex) F) := Nat.find_spec hex
  have hlow : ∀ i < Nat.find hex, IsNilpotent (coeff i F) := by
    intro i hi
    have hni : ¬ IsUnit (coeff i F) := Nat.find_min hex hi
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (coeff i F)
    obtain ⟨b, hb⟩ := hnonunit r (by rw [hr]; exact hni)
    rw [← hr, hb, map_mul]
    exact (Commute.all (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) ϖ)
      (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}) b)).isNilpotent_mul_right hnil
  have hFreg := mem_nonZeroDivisors_of_coeff F (Nat.find hex) hlow hd

  have hprod : F * e (Ideal.Quotient.mk (Ideal.span {U (ϖ ^ m)}) f) = 0 := by
    rw [hFdef, ← map_mul, hsf, map_zero]
  have hqf := (mem_nonZeroDivisors_iff.mp hFreg).1 _ hprod
  exact (map_eq_zero_iff e e.injective).mp hqf

end S_ModularCurve_UVCrossingModel_mem_span_U_of_mul_mem_of_notMem
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_mem_span_U_of_mul_mem_of_notMem (solution)
