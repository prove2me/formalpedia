-- Prove2me | solution 1 for OAI.ShortEgyptian.reciprocal_phase_long_interval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:45:37.575097+00:00
-- url     : https://prove2.me/submissions/f98b75d5-e949-4f08-b4d9-c0d83cc49616

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DeterministicMean.lean:L67-L87
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.reciprocal_phase_long_interval. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_reciprocal_phase_power_bound

-- ---- from OAI.NumberTheory.ShortEgyptian.DeterministicMean ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα uβ

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem sum_nat_int_Icc (f : ℤ → ℂ) (p q : ℕ) :
    (∑ n ∈ Icc p q, f n) = ∑ n ∈ Icc (p : ℤ) q, f n := by
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    simpa only [mem_Icc, Nat.cast_le] using hn
  · intro a _ b _ hab
    exact_mod_cast hab
  · intro n hn
    have hn0 : 0 ≤ n := le_trans (by positivity) (mem_Icc.mp hn).1
    refine ⟨n.toNat, ?_, Int.toNat_of_nonneg hn0⟩
    have hh := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intros
    rfl

theorem dyadic_interval_norm (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C) (p q : ℕ)
    (hp : 1 ≤ p)
    (hlocal : ∀ u v : ℕ, p ≤ u → u ≤ v → v ≤ q → v ≤ 2 * u →
      ‖∑ n ∈ Icc u v, f n‖ ≤ C * u) :
    ‖∑ n ∈ Icc p q, f n‖ ≤ 2 * C * q := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hpq : p ≤ q
    · by_cases hhalf : p ≤ q / 2
      · have hq0 : 0 < q := by omega
        have hleft := ih (q / 2) (Nat.div_lt_self hq0 (by norm_num))
          (fun u v hu huv hv hvu => hlocal u v hu huv (hv.trans (Nat.div_le_self _ _)) hvu)
        have hright := hlocal (q / 2 + 1) q (by omega) (by omega) le_rfl (by omega)
        have heq : Icc p q = Icc p (q / 2) ∪ Icc (q / 2 + 1) q := by
          ext n
          simp only [mem_Icc, mem_union]
          omega
        have hdis : Disjoint (Icc p (q / 2)) (Icc (q / 2 + 1) q) := by
          apply Finset.disjoint_left.mpr
          intro n hn hm
          simp only [mem_Icc] at hn hm
          omega
        rw [heq, Finset.sum_union hdis]
        have hmid : (3 : ℝ) * (q / 2 : ℕ) + 1 ≤ 2 * q := by
          exact_mod_cast (show 3 * (q / 2) + 1 ≤ 2 * q by omega)
        have hh := mul_le_mul_of_nonneg_left hmid hC
        calc
          _ ≤ ‖∑ n ∈ Icc p (q / 2), f n‖ + ‖∑ n ∈ Icc (q / 2 + 1) q, f n‖ := norm_add_le _ _
          _ ≤ 2 * C * (q / 2 : ℕ) + C * (q / 2 + 1 : ℕ) := add_le_add hleft hright
          _ ≤ _ := by push_cast; nlinarith
      · have hh := hlocal p q le_rfl hpq le_rfl (by omega)
        have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
        nlinarith [mul_le_mul_of_nonneg_left hpq' hC, mul_nonneg hC (show (0 : ℝ) ≤ q by positivity)]
    · have he : Icc p q = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
      rw [he, Finset.sum_empty, norm_zero]
      positivity

theorem reciprocal_phase_long_interval (B : ℕ) (T Z : ℝ) (p q : ℕ)
    (hB : 4 ≤ B) (hT : 1 ≤ T) (hp : 1 ≤ p)
    (hlarge : (reciprocalConstantNat B : ℝ) * T ^ reciprocalPower B ≤ p)
    (hZlo : (q : ℝ) ^ 4 ≤ |Z|) (hZhi : |Z| ≤ (p : ℝ) ^ B) :
    ‖∑ n ∈ Icc p q, phase (Z / n)‖ ≤ 16 * q / T := by
  have hT0 : 0 < T := by linarith
  have hh := dyadic_interval_norm (fun n => phase (Z / n)) (8 / T) (by positivity) p q hp
    (by
      intro u v hpu huv hvq hvu
      rw [show (∑ n ∈ Icc u v, phase (Z / n)) =
          ∑ n ∈ Icc (u : ℤ) v, phase (Z / n) from sum_nat_int_Icc (fun n => phase (Z / n)) u v]
      have hu : (p : ℝ) ≤ u := by exact_mod_cast hpu
      have hv : (u : ℝ) ≤ q := by exact_mod_cast huv.trans hvq
      have hb := reciprocal_phase_power_bound B T u Z u v hB hT (hlarge.trans hu)
        ((pow_le_pow_left₀ (by positivity) hv 4).trans hZlo)
        (hZhi.trans (pow_le_pow_left₀ (by positivity) hu B))
        (by simp) (by exact_mod_cast hvu)
      convert hb using 1
      ring)
  convert hh using 1
  ring

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.reciprocal_phase_long_interval := @_root_.OAI.ShortEgyptian.reciprocal_phase_long_interval
