-- Prove2me | solution 1 for ModularCurve.StarBank.eisInt_series
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/98120d6c-91e1-5ce5-8096-cca865364810

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Rat.Lemmas
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_StarBank_eisInt_series

set_option autoImplicit false

open scoped ArithmeticFunction.sigma
open Finset

namespace ModularCurve
namespace W1

theorem eisInt_not_dvd_den_shift {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ ℓ ∣ (bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)).den := by
  have hℓp : ℓ.Prime := Fact.out

  obtain ⟨m, hm⟩ := hℓp.odd_of_ne_two (by omega)
  set k₀ := (ℓ - 1) / 2 with hk₀def
  have h2k₀ : 2 * k₀ = ℓ - 1 := by omega

  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k₀

  rw [h2k₀] at hz
  have hrange : ℓ - 1 + 2 = ℓ + 1 := by omega
  rw [hrange] at hz

  set S := {p ∈ range (ℓ + 1) | p.Prime ∧ p - 1 ∣ ℓ - 1} with hSdef
  have hℓS : ℓ ∈ S := by
    simp only [hSdef, mem_filter, mem_range]
    exact ⟨Nat.lt_succ_self ℓ, hℓp, dvd_refl _⟩

  have hsplit := (add_sum_erase S (fun p => (1 : ℚ) / (p : ℚ)) hℓS).symm
  rw [hsplit] at hz

  have hz' : bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)
      = (z : ℚ) - ∑ p ∈ S.erase ℓ, (1 : ℚ) / (p : ℚ) := by
    linarith [hz]
  rw [hz', Rat.intCast_sub_den]

  have hdendvd := Rat.den_sum_dvd_prod_den (S.erase ℓ) (fun p => (1 : ℚ) / (p : ℚ))
  have hcop : (∏ p ∈ S.erase ℓ, ((1 : ℚ) / (p : ℚ)).den).Coprime ℓ := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    have hpS : p ∈ S := Finset.mem_of_mem_erase hp
    have hpne : p ≠ ℓ := Finset.ne_of_mem_erase hp
    have hpp : p.Prime := (mem_filter.mp hpS).2.1
    have : ((1 : ℚ) / (p : ℚ)).den = p := by simp [hpp.ne_zero]
    rw [this]
    exact (Nat.coprime_primes hpp hℓp).mpr hpne
  intro hdvd
  exact (Nat.Prime.coprime_iff_not_dvd hℓp).mp
    (Nat.Coprime.of_dvd_left hdendvd hcop).symm hdvd

end ModularCurve.W1

theorem ModularCurve.StarBank.eisInt_dvd_den {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ℓ ∣ (bernoulli (ℓ - 1)).den := by
  have hℓp : ℓ.Prime := Fact.out
  have hshift := ModularCurve.W1.eisInt_not_dvd_den_shift hℓ5

  have hℓden : ((1 : ℚ) / (ℓ : ℚ)).den = ℓ := by simp [hℓp.ne_zero]
  have hdvd : ℓ ∣ (bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)).den * (bernoulli (ℓ - 1)).den := by
    have h := Rat.sub_den_dvd (bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)) (bernoulli (ℓ - 1))
    have hsimp : bernoulli (ℓ - 1) + 1 / (ℓ : ℚ) - bernoulli (ℓ - 1) = 1 / (ℓ : ℚ) := by ring
    rw [hsimp, hℓden] at h
    exact h
  exact ((hℓp.dvd_mul).mp hdvd).resolve_left hshift

private theorem ModularCurve.StarBank.eisInt_not_dvd_num {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ (ℓ : ℤ) ∣ (bernoulli (ℓ - 1)).num := by
  intro hdvd
  have hden := ModularCurve.StarBank.eisInt_dvd_den hℓ5
  have hnum : ℓ ∣ (bernoulli (ℓ - 1)).num.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have hcop := (bernoulli (ℓ - 1)).reduced
  have hgcd : ℓ ∣ Nat.gcd (bernoulli (ℓ - 1)).num.natAbs (bernoulli (ℓ - 1)).den :=
    Nat.dvd_gcd hnum hden
  unfold Nat.Coprime at hcop
  rw [hcop] at hgcd
  exact (Nat.Prime.one_lt (Fact.out : ℓ.Prime)).ne' (Nat.dvd_one.mp hgcd)

theorem ModularCurve.StarBank.eisInt_bernoulli_ne_zero
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) : bernoulli (ℓ - 1) ≠ 0 := by
  intro h
  have := ModularCurve.StarBank.eisInt_dvd_den hℓ5
  rw [h, Rat.den_zero] at this
  exact (Nat.Prime.one_lt (Fact.out : ℓ.Prime)).ne' (Nat.dvd_one.mp this)

theorem ModularCurve.StarBank.eisInt_coeff {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hk : 3 ≤ ℓ - 1) (m : ℕ) :
    ∃ z : ℤ, ((bernoulli (ℓ - 1)).num : ℂ)
          * (UpperHalfPlane.qExpansion 1 (ModularForm.E hk)).coeff m = ↑z
        ∧ (m = 0 → z = (bernoulli (ℓ - 1)).num) ∧ (1 ≤ m → (ℓ : ℤ) ∣ z) := by
  classical
  have hℓp : ℓ.Prime := Fact.out
  have hkeven : Even (ℓ - 1) := by
    obtain ⟨c, hc⟩ := hℓp.odd_of_ne_two (by omega); exact ⟨c, by omega⟩
  set B := bernoulli (ℓ - 1) with hBdef
  have hB0 : B ≠ 0 := ModularCurve.StarBank.eisInt_bernoulli_ne_zero hℓ5
  have hcoeff := EisensteinSeries.E_qExpansion_coeff hk hkeven m
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0
    refine ⟨B.num, ?_, fun _ => rfl, by omega⟩
    rw [hcoeff]; simp
  ·
    have hm1' : m ≠ 0 := hm1.ne'
    rw [hcoeff, if_neg hm1']
    refine ⟨-(2 * (↑(ℓ - 1) : ℤ) * (↑B.den : ℤ) * (↑(σ (ℓ - 1 - 1) m) : ℤ)), ?_, ?_, ?_⟩
    ·
      have hnum : (B.num : ℂ) ≠ 0 := by
        exact_mod_cast Rat.num_ne_zero.mpr hB0
      have hcast : ((B : ℚ) : ℂ) = (B.num : ℂ) / (B.den : ℂ) := by
        exact_mod_cast Rat.cast_def (K := ℂ) B
      rw [hcast]
      have hden0 : (B.den : ℂ) ≠ 0 := by
        exact_mod_cast B.den_ne_zero
      field_simp
      push_cast
      ring
    · intro h; omega
    · intro _
      have hd : (ℓ : ℤ) ∣ (↑B.den : ℤ) :=
        Int.natCast_dvd_natCast.mpr (ModularCurve.StarBank.eisInt_dvd_den hℓ5)
      exact dvd_neg.mpr ((hd.mul_left _).mul_right _)

private theorem ModularCurve.StarBank.eisInt_series {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hk : 3 ≤ ℓ - 1) :
    ∃ T : PowerSeries ℤ,
      T.map (Int.castRingHom ℂ)
        = ((bernoulli (ℓ - 1)).num : ℂ) • UpperHalfPlane.qExpansion 1 (⇑(ModularForm.E hk))
      ∧ PowerSeries.constantCoeff T = (bernoulli (ℓ - 1)).num
      ∧ ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m := by
  classical
  refine ⟨PowerSeries.mk fun m => (ModularCurve.StarBank.eisInt_coeff hℓ5 hk m).choose,
    ?_, ?_, ?_⟩
  · ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_smul, smul_eq_mul]
    exact (ModularCurve.StarBank.eisInt_coeff hℓ5 hk m).choose_spec.1.symm
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact (ModularCurve.StarBank.eisInt_coeff hℓ5 hk 0).choose_spec.2.1 rfl
  · intro m hm
    rw [PowerSeries.coeff_mk]
    exact (ModularCurve.StarBank.eisInt_coeff hℓ5 hk m).choose_spec.2.2 hm

example : ¬ (7 : ℤ) ∣ (-240 : ℤ) := by decide

open scoped ArithmeticFunction.sigma
open Finset in

theorem solution {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hk : 3 ≤ ℓ - 1) :
    ∃ T : PowerSeries ℤ,
      T.map (Int.castRingHom ℂ)
        = ((bernoulli (ℓ - 1)).num : ℂ) • UpperHalfPlane.qExpansion 1 (⇑(ModularForm.E hk))
      ∧ PowerSeries.constantCoeff T = (bernoulli (ℓ - 1)).num
      ∧ ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m :=
  ModularCurve.StarBank.eisInt_series hℓ5 hk

#print axioms solution

end S_ModularCurve_StarBank_eisInt_series
end P2MW
export P2MW.S_ModularCurve_StarBank_eisInt_series (solution)
