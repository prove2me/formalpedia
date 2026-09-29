-- Prove2me | solution 1 for MTT.measure_extension
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-06T01:44:29.000443+00:00
-- url     : https://prove2.me/submissions/68b5a2e8-d2ad-4ea7-9d7f-6be6321f5bed

import Theorems.Thm_PadicMeasure_colmez_r0_moment_extension
import Theorems.Thm_MTT_ordinary_centered_disk_bound
import Theorems.Thm_MTT_distribution_relation
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
noncomputable section
open MTT MeasureTheory
open scoped BigOperators

private lemma integral_zero_periodic {N k : ℕ}
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (z : ℤ) :
    modularIntegral f (Polynomial.X^0) (r+z) = modularIntegral f (Polynomial.X^0) r := by
  have hp := SlashInvariantFormClass.periodic_comp_ofComplex f
    (show (1 : ℝ) ∈ (GammaOne N).strictPeriods by
      simp [GammaOne, CongruenceSubgroup.strictPeriods_Gamma1])
  unfold modularIntegral
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [pow_zero, Polynomial.eval_one, mul_one]
  have h := hp.int_mul z ((r : ℂ)+Complex.I*t)
  simpa [Function.comp_def, add_assoc, add_comm, add_left_comm] using h

private lemma value_zero_periodic {N k : ℕ} (_hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (f : Eigenform N k ι) (P : Periods k ι f.form)
    (s : Bool) (r : ℚ) (z : ℤ) : P.value s 0 (r+z) = P.value s 0 r := by
  apply ι.injective
  rw [P.comparison s 0 _ (by omega), P.comparison s 0 _ (by omega)]
  unfold signedIntegral
  rw [integral_zero_periodic]
  have he : -(r+(z : ℚ)) = -r+(-z : ℤ) := by push_cast; ring
  rw [he, integral_zero_periodic]

open MTT in
private lemma mtt_mass_residue_invariance
    {p N k : ℕ} [Fact p.Prime] (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (s : Bool)
    (n : ℕ) (hn : 0 < n) (a b : ℤ)
    (hab : (a : ZMod (p ^ n)) = (b : ZMod (p ^ n))) :
    diskMoment f ιp P α s 0 n a = diskMoment f ιp P α s 0 n b := by
  have hd : ((p^n : ℕ) : ℤ) ∣ a-b := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hab.symm
  have hval (l : ℕ) (hl : l ≤ n) :
      P.value s 0 (-(a : ℚ)/(p : ℚ)^l) = P.value s 0 (-(b : ℚ)/(p : ℚ)^l) := by
    have hdiv : ((p^l : ℕ) : ℤ) ∣ a-b :=
      dvd_trans (by exact_mod_cast (pow_dvd_pow p hl)) hd
    obtain ⟨z,hz⟩ := hdiv
    have he : -(a : ℚ)/(p : ℚ)^l = -(b : ℚ)/(p : ℚ)^l + (-z : ℤ) := by
      have hz' : (a : ℚ)-b = (p : ℚ)^l*z := by exact_mod_cast hz
      have hpn : (p : ℚ)^l ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
      push_cast
      field_simp
      linear_combination -hz'
    rw [he, value_zero_periodic hk ι f P s]
  simp only [diskMoment, algebraicSymbol, zero_add, Finset.sum_range_one,
    Nat.choose_zero_right, Nat.cast_one, Nat.sub_self, pow_zero, mul_one, one_mul]
  rw [hval n le_rfl, hval (n-1) (by omega)]

open MTT in
theorem solution
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α)
    (s : Bool) :
    ∃! μ : UnitMeasure p, RealizesMoments f ιp P α s μ := by
  obtain ⟨C, hC, hbound⟩ := ordinary_centered_disk_bound hN hk ι ιp f P α hα
  have hres : ∀ (n : ℕ), 0 < n → ∀ (a b : ℤ),
      IsCoprime a (p : ℤ) → IsCoprime b (p : ℤ) →
      (a : ZMod (p^n)) = (b : ZMod (p^n)) →
      diskMoment f ιp P α s 0 n a = diskMoment f ιp P α s 0 n b := by
    intro n hn a b _ _ hab
    exact mtt_mass_residue_invariance hk ι ιp f P α s n hn a b hab
  have hadd : ∀ (j : ℕ), j ≤ k-2 → ∀ (n : ℕ), 0 < n →
      ∀ (a : ℤ), IsCoprime a (p : ℤ) →
        (∑ b ∈ Finset.range p, diskMoment f ιp P α s j (n+1)
          (a+(b : ℤ)*(p : ℤ)^n)) = diskMoment f ιp P α s j n a := by
    intro j hj n hn a _
    exact distribution_relation hN hk ι ιp f P α hα s j hj n hn a
  have h := PadicMeasure.colmez_r0_moment_extension (k-2)
    (diskMoment f ιp P α s) hres hadd ⟨C, hC, fun n hn a _ j hj => hbound s n hn a j hj⟩
  simpa only [RealizesMoments, diskFunction, coordinate, UnitMeasure] using h
