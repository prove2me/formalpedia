-- Prove2me | solution 1 for MazurTransfer.rational_thirteen_power_class_dimension_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T05:30:19.385227+00:00
-- url     : https://prove2.me/submissions/0175819d-6045-48c1-9baa-d55c181f1ac4

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0. Design boundary: publish the checked rational nineteenth-power quotient and valuation interface. Named downstream consumer: the actual selected pi Selmer dimension bound. -/
import Definitions.Def_MazurTransfer_RationalNineteenthPowerValuations

noncomputable section
namespace MazurTransfer.NineteenthPowersFromPrimeValuations
open scoped BigOperators

theorem nat_exists_nineteenth_root (n : ℕ) (hn : n ≠ 0)
    (hval : ∀ p : ℕ, p.Prime → 19 ∣ padicValNat p n) :
    ∃ r : ℕ, r ^ 19 = n := by
  let r := n.factorization.prod (fun p k => p ^ (k / 19))
  refine ⟨r, ?_⟩
  calc
    r ^ 19 = n.factorization.prod (fun p k => p ^ k) := by
      change (∏ p ∈ n.factorization.support, p ^ (n.factorization p / 19)) ^ 19 =
        ∏ p ∈ n.factorization.support, p ^ n.factorization p
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul, Nat.div_mul_cancel]
      rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
      exact hval p (Nat.prime_of_mem_primeFactors hp)
    _ = n := Nat.prod_factorization_pow_eq_self hn

theorem rat_num_den_valuation_divisibility (a : ℚ)
    (hval : ∀ p : ℕ, p.Prime → (19 : ℤ) ∣ padicValRat p a)
    (p : ℕ) (hp : p.Prime) :
    19 ∣ padicValNat p a.num.natAbs ∧ 19 ∣ padicValNat p a.den := by
  by_cases hd : p ∣ a.den
  · have hn : ¬ p ∣ a.num.natAbs := by
      intro hn
      have h := Nat.dvd_gcd hn hd
      rw [a.reduced.gcd_eq_one] at h
      exact hp.ne_one (Nat.dvd_one.mp h)
    have h := hval p hp
    rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hn] at h
    have h' : (19 : ℤ) ∣ -(padicValNat p a.den : ℤ) := by simpa using h
    refine ⟨?_, ?_⟩
    · rw [padicValNat.eq_zero_of_not_dvd hn]
      exact dvd_zero _
    · exact_mod_cast (Int.dvd_neg.mp h')
  · have h := hval p hp
    rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hd] at h
    have h' : (19 : ℤ) ∣ (padicValNat p a.num.natAbs : ℤ) := by simpa using h
    refine ⟨?_, ?_⟩
    · exact_mod_cast h'
    · rw [padicValNat.eq_zero_of_not_dvd hd]
      exact dvd_zero _

theorem int_exists_nineteenth_root (n : ℤ) (hn : n ≠ 0)
    (hval : ∀ p : ℕ, p.Prime → 19 ∣ padicValNat p n.natAbs) :
    ∃ r : ℤ, r ^ 19 = n := by
  obtain ⟨r, hr⟩ := nat_exists_nineteenth_root n.natAbs (Int.natAbs_ne_zero.mpr hn) hval
  have hcast : (r : ℤ) ^ 19 = (n.natAbs : ℤ) := by exact_mod_cast hr
  by_cases h : 0 ≤ n
  · refine ⟨r, ?_⟩
    rw [hcast, Int.natCast_natAbs, abs_of_nonneg h]
  · refine ⟨-(r : ℤ), ?_⟩
    rw [show (-(r : ℤ)) ^ 19 = -((r : ℤ) ^ 19) by ring, hcast,
      Int.natCast_natAbs, abs_of_neg (lt_of_not_ge h), neg_neg]

theorem rat_exists_nineteenth_root (a : ℚ) (ha : a ≠ 0)
    (hval : ∀ p : ℕ, p.Prime → (19 : ℤ) ∣ padicValRat p a) :
    ∃ b : ℚ, b ^ 19 = a := by
  obtain ⟨n, hn⟩ := int_exists_nineteenth_root a.num (Rat.num_ne_zero.mpr ha)
    (fun p hp => (rat_num_den_valuation_divisibility a hval p hp).1)
  obtain ⟨d, hd⟩ := nat_exists_nineteenth_root a.den a.den_nz
    (fun p hp => (rat_num_den_valuation_divisibility a hval p hp).2)
  refine ⟨(n : ℚ) / (d : ℚ), ?_⟩
  rw [div_pow, ← Int.cast_pow, hn, ← Nat.cast_pow, hd]
  exact Rat.num_div_den a

theorem unit_exists_nineteenth_root (a : ℚˣ)
    (hval : ∀ p : ℕ, p.Prime → (19 : ℤ) ∣ padicValRat p (a : ℚ)) :
    ∃ b : ℚˣ, b ^ 19 = a := by
  obtain ⟨b, hb⟩ := rat_exists_nineteenth_root (a : ℚ) (Units.ne_zero a) hval
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hb
    exact (Units.ne_zero a) hb.symm
  exact ⟨Units.mk0 b hb0, Units.ext hb⟩

end MazurTransfer.NineteenthPowersFromPrimeValuations
end

noncomputable section
namespace MazurTransfer.RationalNineteenthPowerValuations
open RationalNineteenthPowerClasses NineteenthPowersFromPrimeValuations
local instance : Module (ZMod 19) (Additive PowerClasses) := powerClassesZModModule

theorem class_eq_one_of_all_prime_values (y : PowerClasses)
    (h : ∀ (p : ℕ) (hp : p.Prime), valuationClassHom p hp y = 1) : y = 1 := by
  revert h
  refine Quotient.inductionOn y ?_
  intro a ha
  apply (classOf_eq_one_iff a).mpr
  apply unit_exists_nineteenth_root a
  intro p hp
  have h := congrArg Multiplicative.toAdd (ha p hp)
  change ((padicValRat p (a : ℚ) : ℤ) : ZMod 19) = 0 at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

theorem zero_of_all_prime_values (x : Additive PowerClasses)
    (h : ∀ (p : ℕ) (hp : p.Prime), valuationLinearMap p hp x = 0) : x = 0 := by
  apply Additive.toMul.injective
  apply class_eq_one_of_all_prime_values x.toMul
  intro p hp
  exact congrArg Multiplicative.ofAdd (h p hp)

end MazurTransfer.RationalNineteenthPowerValuations
end

noncomputable section
namespace MazurTransfer.RationalThirteenPowerClassBound
open RationalNineteenthPowerClasses RationalNineteenthPowerValuations
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : Module (ZMod 19) (Additive PowerClasses) := powerClassesZModModule

theorem thirteenCoordinate_injective : Function.Injective thirteenCoordinate := by
  intro x y h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply zero_of_all_prime_values (x.val - y.val)
  intro q hq
  by_cases h13 : q = 13
  · subst q
    rw [map_sub]
    exact sub_eq_zero.mpr h
  · rw [map_sub, (mem_thirteenSupport x.val).mp x.property q hq h13,
      (mem_thirteenSupport y.val).mp y.property q hq h13, sub_self]

theorem thirteenSupport_finiteDimensional : FiniteDimensional (ZMod 19) thirteenSupport :=
  FiniteDimensional.of_injective thirteenCoordinate thirteenCoordinate_injective

theorem thirteenSupport_finrank_le_one : Module.finrank (ZMod 19) thirteenSupport ≤ 1 := by
  simpa only [Module.finrank_self] using
    thirteenCoordinate.finrank_le_finrank_of_injective thirteenCoordinate_injective

end MazurTransfer.RationalThirteenPowerClassBound
end

open MazurTransfer.RationalNineteenthPowerClasses MazurTransfer.RationalThirteenPowerClassBound
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : Module (ZMod 19) (Additive PowerClasses) := powerClassesZModModule

theorem solution :
    FiniteDimensional (ZMod 19) thirteenSupport ∧ Module.finrank (ZMod 19) thirteenSupport ≤ 1 :=
  ⟨thirteenSupport_finiteDimensional, thirteenSupport_finrank_le_one⟩
#print axioms solution
