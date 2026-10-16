-- Prove2me | solution 1 for OAI.ShortEgyptian.prime_reciprocals_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:50:37.247139+00:00
-- url     : https://prove2.me/submissions/95c3f8f9-9cab-4ea5-95b1-89761782e472

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/PrimeReciprocals.lean:L37-L81
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.prime_reciprocals_dyadic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeReciprocals ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem prime_reciprocals_band (s : Finset ℕ) (R : ℝ) (hR : 1 < R)
    (hs : ∀ p ∈ s, p.Prime ∧ R ≤ p ∧ (p : ℝ) ≤ 2 * R) :
    ∑ p ∈ s, (1 : ℝ) / p ≤ 2 * Real.log 4 / Real.log R := by
  have hRp : 0 < R := lt_trans zero_lt_one hR
  have hl : 0 < Real.log R := Real.log_pos hR
  have hsub : s ⊆ Nat.primesLE ⌊2 * R⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hs p hp).2.2, (hs p hp).1⟩
  have hsum : ∑ p ∈ s, Real.log p ≤ Real.log 4 * (2 * R) := by
    calc
      _ ≤ ∑ p ∈ Nat.primesLE ⌊2 * R⌋₊, Real.log p :=
        sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
      _ = Chebyshev.theta (2 * R) := (Chebyshev.theta_eq_sum_primesLE _).symm
      _ ≤ _ := Chebyshev.theta_le_log4_mul_x (by positivity)
  calc
    _ ≤ ∑ p ∈ s, Real.log p / (R * Real.log R) := by
      apply sum_le_sum
      intro p hp
      have hpp : 0 < (p : ℝ) := lt_of_lt_of_le hRp (hs p hp).2.1
      apply (div_le_div_iff₀ hpp (mul_pos hRp hl)).mpr
      have hlog := Real.log_le_log hRp (hs p hp).2.1
      nlinarith [mul_le_mul_of_nonneg_left hlog hpp.le,
        mul_le_mul_of_nonneg_right (hs p hp).2.1 hl.le]
    _ = (∑ p ∈ s, Real.log p) / (R * Real.log R) := (sum_div _ _ _).symm
    _ ≤ (Real.log 4 * (2 * R)) / (R * Real.log R) := by gcongr
    _ = _ := by field_simp

theorem prime_reciprocals_dyadic (K : ℕ) :
    ∑ p ∈ Nat.primesLE (2 ^ (K + 1)), (1 : ℝ) / p ≤ 4 * (1 + (harmonic K : ℝ)) := by
  induction K with
  | zero =>
    have h : Nat.primesLE 2 = {2} := by decide
    norm_num [h]
  | succ K ih =>
    let s := (Nat.primesLE (2 ^ (K + 1 + 1))).filter fun p => 2 ^ (K + 1) < p
    have hsplit :
        ∑ p ∈ Nat.primesLE (2 ^ (K + 1 + 1)), (1 : ℝ) / p =
        (∑ p ∈ Nat.primesLE (2 ^ (K + 1)), (1 : ℝ) / p) + ∑ p ∈ s, (1 : ℝ) / p := by
      rw [← sum_filter_add_sum_filter_not _ (fun p => p ≤ 2 ^ (K + 1))]
      congr 1
      · congr 1
        ext p
        simp only [mem_filter, Nat.mem_primesLE]
        have hp : 2 ^ (K + 1) ≤ 2 ^ (K + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1.trans hp, h2⟩, h1⟩
      · simp [s]
    have hb := prime_reciprocals_band s ((2 : ℝ) ^ (K + 1))
      (by exact one_lt_pow₀ (by norm_num) (by omega)) (by
        intro p hp
        obtain ⟨hp, hp'⟩ := mem_filter.mp hp
        obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hp
        refine ⟨hprime, ?_, ?_⟩
        · exact_mod_cast hp'.le
        · have hle' : (p : ℝ) ≤ (2 : ℝ) ^ (K + 1 + 1) := by exact_mod_cast hle
          simpa [pow_succ, mul_comm] using hle')
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      convert Real.log_pow 2 2 using 1 <;> norm_num
    rw [Real.log_pow, hlog4] at hb
    have hb' : ∑ p ∈ s, (1 : ℝ) / p ≤ 4 / (K + 1 : ℕ) := by
      convert hb using 1
      field_simp
      norm_num
    rw [hsplit, harmonic_succ]
    push_cast
    push_cast at hb'
    rw [div_eq_mul_inv] at hb'
    linarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.prime_reciprocals_dyadic := @_root_.OAI.ShortEgyptian.prime_reciprocals_dyadic
