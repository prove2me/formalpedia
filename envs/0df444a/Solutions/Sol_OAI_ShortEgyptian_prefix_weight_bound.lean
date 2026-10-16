-- Prove2me | solution 1 for OAI.ShortEgyptian.prefix_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:18:26.457481+00:00
-- url     : https://prove2.me/submissions/540eadbf-da9d-4bce-b30a-896e0b45c123

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/SmoothBounds.lean:L107-L126
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.prefix_weight_bound. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Theorems.Thm_OAI_ShortEgyptian_rough_truncated_bound
import Theorems.Thm_OAI_ShortEgyptian_truncatedDivisors_mul

-- ---- from OAI.NumberTheory.ShortEgyptian.SmoothBounds ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem rough_exponential_bound {n : ℕ} (hn : n ≠ 0) (v W z : ℝ)
    (hv : 0 < v) (hvW : v < W) (hz : 1 < z) (hW : Real.log n ≤ W)
    (hrough : ∀ p ∈ n.primeFactorsList, z ≤ p) :
    (truncatedDivisorCount (Real.exp v) n:ℝ) ≤
      Real.exp ((1+Real.log (W/v))*v/Real.log z) := by
  have hW0 : 0 < W := hv.trans hvW
  have hq : 0 < v/W := div_pos hv hW0
  have hq1 : v/W < 1 := (div_lt_one hW0).mpr hvW
  have hb := rough_truncated_bound hn (Real.exp v) W z (v/W) hz hq hq1 hW hrough
  rw [Real.log_exp, Real.log_div hv.ne' hW0.ne'] at hb
  rw [Real.log_div hW0.ne' hv.ne']
  convert hb using 1
  congr 1
  field_simp
  ring

theorem prefix_weight_bound {n d e p : ℕ} (hde : n = d*e)
    (hd : d ≠ 0) (he : e ≠ 0) (hp : p.Prime) (r : ℕ) (v W : ℝ)
    (hv : 0 < v) (hvW : v < W) (hnW : Real.log n ≤ W)
    (hr : ∀ q ∈ e.primeFactorsList, p ≤ q) :
    (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤ (d.divisors.card:ℝ)^r *
      Real.exp ((r:ℝ)*(1+Real.log (W/v))*v/Real.log p) := by
  have hele : (e:ℝ) ≤ n := by
    exact_mod_cast (Nat.le_of_dvd (by rw [hde]; exact Nat.mul_pos (Nat.pos_of_ne_zero hd) (Nat.pos_of_ne_zero he))
      (hde ▸ dvd_mul_left e d))
  have hrough := rough_exponential_bound he v W p hv hvW (by exact_mod_cast hp.one_lt)
    ((Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero he) hele).trans hnW)
    (fun q hq => by exact_mod_cast hr q hq)
  have hmul : (truncatedDivisorCount (Real.exp v) n:ℝ) ≤
      (d.divisors.card:ℝ)*truncatedDivisorCount (Real.exp v) e := by
    rw [hde]
    exact_mod_cast truncatedDivisors_mul (Real.exp v) hd he
  calc
    _ ≤ ((d.divisors.card:ℝ)*truncatedDivisorCount (Real.exp v) e)^r := pow_le_pow_left₀ (Nat.cast_nonneg _) hmul r
    _ ≤ ((d.divisors.card:ℝ)*Real.exp ((1+Real.log (W/v))*v/Real.log p))^r := by gcongr
    _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.prefix_weight_bound := @_root_.OAI.ShortEgyptian.prefix_weight_bound
