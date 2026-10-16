-- Prove2me | solution 1 for OAI.ShortEgyptian.polynomial_geom_local
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:56:05.033092+00:00
-- url     : https://prove2.me/submissions/4c0e78ae-2309-4881-b04f-b24eef521e91

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DivisorWeights.lean:L24-L47
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.polynomial_geom_local. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights

-- ---- from OAI.NumberTheory.ShortEgyptian.DivisorWeights ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem summable_shifted_geom (r k : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Summable (fun j : ℕ => ((j + k : ℕ) : ℝ)^r * x^j) := by
  have hb : Summable (fun j : ℕ => (j : ℝ)^r * x^j) :=
    summable_pow_mul_geometric_of_norm_lt_one r (by simpa [Real.norm_eq_abs, abs_of_pos hx0] using hx1)
  have hs := (summable_nat_add_iff k).mpr hb
  have hs' := hs.mul_right (x ^ k)⁻¹
  apply hs'.congr
  intro j
  rw [pow_add]
  field_simp

theorem polynomial_geom_local (r : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 3/4) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ)^r * x^j) ∧
    (∑' j : ℕ, ((j + 1 : ℕ) : ℝ)^r * x^j) ≤ Real.exp (momentSeriesConst r * x) := by
  have hs (k : ℕ) := summable_shifted_geom r k (3/4) (by norm_num) (by norm_num)
  have hsum (k : ℕ) : Summable (fun j : ℕ => ((j+k:ℕ):ℝ)^r * x^j) := by
    apply Summable.of_nonneg_of_le (fun j => by positivity) _ (hs k)
    intro j
    gcongr
  refine ⟨hsum 1, ?_⟩
  have htail : (∑' j : ℕ, ((j+2:ℕ):ℝ)^r * x^j) ≤ momentSeriesConst r := by
    exact (hsum 2).tsum_le_tsum (fun j => by gcongr) (hs 2)
  rw [(hsum 1).tsum_eq_zero_add]
  simp only [Nat.zero_add, Nat.cast_one, one_pow, pow_zero, mul_one]
  have heq : (∑' b : ℕ, ((b + 1 + 1 : ℕ) : ℝ)^r * x^(b+1)) =
      x * ∑' b : ℕ, ((b+2:ℕ):ℝ)^r * x^b := by
    rw [← tsum_mul_left]
    congr 1
    ext b
    simp only [pow_succ]
    ring
  rw [heq]
  calc
    _ ≤ 1 + momentSeriesConst r * x := by nlinarith
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (momentSeriesConst r * x)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.polynomial_geom_local := @_root_.OAI.ShortEgyptian.polynomial_geom_local
