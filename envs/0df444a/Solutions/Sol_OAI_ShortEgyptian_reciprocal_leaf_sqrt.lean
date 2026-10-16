-- Prove2me | solution 1 for OAI.ShortEgyptian.reciprocal_leaf_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:25:26.247845+00:00
-- url     : https://prove2.me/submissions/bf12fdaf-f6a4-45f9-a77f-be30870a19f3

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ReciprocalEstimates.lean:L10-L84
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.reciprocal_leaf_sqrt. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Theorems.Thm_OAI_ShortEgyptian_backwardDifferences_reciprocal_bounds
import Theorems.Thm_OAI_ShortEgyptian_phase_sum_second_derivative_int

-- ---- from OAI.NumberTheory.ShortEgyptian.IteratedDifferencing ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem backwardDifferences_smul (hs : List ℝ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    backwardDifferences hs (fun y => c * f y) x = c * backwardDifferences hs f x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih => simp only [backwardDifferences, ih]; ring

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ReciprocalEstimates ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem reciprocal_leaf_sqrt (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    (Z U : ℝ) (p q : ℤ) (hZ : 0 ≤ Z) (hU : 1 ≤ U)
    (hp : U ≤ p) (hq : (q : ℝ) + hs.sum ≤ 2 * U) (hpq : p ≤ q)
    (lam : ℝ) (hlamdef : lam =
      Z * (hs.prod * (hs.length + 2).factorial * (1 / (3 * U)) ^ (hs.length + 3)))
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    ‖∑ n ∈ Icc p q, phase (backwardDifferences hs (fun x => Z / x) n)‖ ≤
      6 * (3 : ℝ) ^ (hs.length + 3) * U * Real.sqrt lam + 6 / Real.sqrt lam + 6 := by
  have hU0 : 0 < U := by linarith
  have hsum : 0 ≤ hs.sum := List.sum_nonneg hhs
  have hfun : (fun x : ℝ => Z / x) = (fun x => Z * (1 / x)) := by
    ext x; ring
  have hstep (n : ℤ) (hn : n ∈ Ico p q) :
      lam ≤ (backwardDifferences hs (fun x => Z / x) (n + 2) -
        backwardDifferences hs (fun x => Z / x) (n + 1)) -
        (backwardDifferences hs (fun x => Z / x) (n + 1) -
        backwardDifferences hs (fun x => Z / x) n) ∧
      (backwardDifferences hs (fun x => Z / x) (n + 2) -
        backwardDifferences hs (fun x => Z / x) (n + 1)) -
        (backwardDifferences hs (fun x => Z / x) (n + 1) -
        backwardDifferences hs (fun x => Z / x) n) ≤
        (3 : ℝ) ^ (hs.length + 3) * lam := by
    have hn' := mem_Ico.mp hn
    have hnU : U ≤ (n : ℝ) := hp.trans (by exact_mod_cast hn'.1)
    have hnq : (n : ℝ) + 1 ≤ q := by exact_mod_cast hn'.2
    have hxV : (n : ℝ) + (1 :: 1 :: hs).sum ≤ 3 * U := by
      simp only [List.sum_cons]
      linarith
    have hb := backwardDifferences_reciprocal_bounds (1 :: 1 :: hs) (by
      intro h hh
      simp only [List.mem_cons] at hh
      rcases hh with rfl | rfl | hh
      · norm_num
      · norm_num
      · exact hhs h hh) hU0 hnU hxV
    simp only [List.prod_cons, one_mul, List.length_cons] at hb
    have hlen2 : hs.length + 1 + 1 = hs.length + 2 := by omega
    have hlen3 : hs.length + 1 + 1 + 1 = hs.length + 3 := by omega
    rw [hlen2, hlen3] at hb
    have hd : (backwardDifferences hs (fun x => Z / x) (n + 2) -
        backwardDifferences hs (fun x => Z / x) (n + 1)) -
        (backwardDifferences hs (fun x => Z / x) (n + 1) -
        backwardDifferences hs (fun x => Z / x) n) =
        Z * backwardDifferences (1 :: 1 :: hs) (fun x => 1 / x) n := by
      rw [hfun]
      simp only [backwardDifferences_smul, backwardDifferences]
      rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
      ring
    rw [hd, hlamdef]
    constructor
    · exact mul_le_mul_of_nonneg_left hb.1 hZ
    · have hident : (1 / U) ^ (hs.length + 3) =
          (3 : ℝ) ^ (hs.length + 3) * (1 / (3 * U)) ^ (hs.length + 3) := by
        rw [← mul_pow]
        congr 1
        field_simp
      have hh := mul_le_mul_of_nonneg_left hb.2 hZ
      rw [hident] at hh
      have heq : Z * (hs.prod * ↑(hs.length + 2).factorial *
          (3 ^ (hs.length + 3) * (1 / (3 * U)) ^ (hs.length + 3))) =
          3 ^ (hs.length + 3) * (Z * (hs.prod * ↑(hs.length + 2).factorial *
          (1 / (3 * U)) ^ (hs.length + 3))) := by ring
      rw [heq] at hh
      exact hh
  have hh := phase_sum_second_derivative_int
    (fun n => backwardDifferences hs (fun x => Z / x) n) p q hpq
    hlam hlam1 (by positivity : (0 : ℝ) ≤ 3 ^ (hs.length + 3)) (by
      intro n hn
      simpa only [Int.cast_add, Int.cast_ofNat, Int.cast_one] using hstep n hn)
  have hlength : (q - p : ℤ) ≤ U := by
    push_cast
    linarith
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_right hlength (show 0 ≤ 6 * (3 : ℝ) ^ (hs.length + 3) * Real.sqrt lam by positivity)
  nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.reciprocal_leaf_sqrt := @_root_.OAI.ShortEgyptian.reciprocal_leaf_sqrt
