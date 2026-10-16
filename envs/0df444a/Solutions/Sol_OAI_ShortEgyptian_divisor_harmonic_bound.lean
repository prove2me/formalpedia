-- Prove2me | solution 1 for OAI.ShortEgyptian.divisor_harmonic_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:16:44.921047+00:00
-- url     : https://prove2.me/submissions/f9568d6f-34c4-4f39-81dc-92557ddcdfd3

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/SmoothBounds.lean:L74-L89
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.divisor_harmonic_bound. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_prime_reciprocals_bound
import Theorems.Thm_OAI_ShortEgyptian_smooth_divisor_weight

-- ---- from OAI.NumberTheory.ShortEgyptian.DivisorWeights ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem momentSeriesConst_nonneg (r : ℕ) : 0 ≤ momentSeriesConst r := by
  exact tsum_nonneg (fun _ => by positivity)

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.SmoothBounds ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem prime_reciprocals_real (T : ℝ) (hT : 2 ≤ T) :
    ∑ p ∈ Nat.primesLE ⌊T⌋₊, (1:ℝ)/p ≤ primeRecipBound T := by
  have h2 : 2 ≤ ⌊T⌋₊ := Nat.le_floor hT
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (prime_reciprocals_bound ⌊T⌋₊ h2).trans
  have hlog := Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊T⌋₊))
    (Nat.floor_le (by linarith : 0 ≤ T))
  have hh : 0 ≤ Real.log (⌊T⌋₊:ℝ) := Real.log_natCast_nonneg _
  have harg : 0 < 1+Real.log (⌊T⌋₊:ℝ)/Real.log 2 := by positivity
  have hlog' := Real.log_le_log harg (show 1+Real.log (⌊T⌋₊:ℝ)/Real.log 2 ≤ 1+Real.log T/Real.log 2 by gcongr)
  unfold primeRecipBound
  linarith

theorem factored_primesLE {n : ℕ} (hn : n ≠ 0) {T : ℝ}
    (hs : ∀ p ∈ n.primeFactorsList, (p:ℝ) ≤ T) :
    n ∈ Nat.factoredNumbers (Nat.primesLE ⌊T⌋₊) := by
  refine ⟨hn, ?_⟩
  intro p hp
  exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hs p hp), Nat.prime_of_mem_primeFactorsList hp⟩

theorem divisor_harmonic_bound (r : ℕ) (T : ℝ) (hT : 2 ≤ T) :
    ∑ d ∈ Icc 1 ⌊T⌋₊, (d.divisors.card:ℝ)^r/d ≤
      Real.exp (momentSeriesConst r * primeRecipBound T) := by
  have hf : ∀ d ∈ Icc 1 ⌊T⌋₊, d ∈ Nat.factoredNumbers (Nat.primesLE ⌊T⌋₊) := by
    intro d hd
    have hd' := mem_Icc.mp hd
    apply factored_primesLE (by omega)
    intro p hp
    apply le_trans _ (Nat.floor_le (by linarith : 0 ≤ T))
    exact_mod_cast (Nat.le_of_dvd (by omega : 0 < d) (Nat.dvd_of_mem_primeFactorsList hp)).trans hd'.2
  have hh := smooth_divisor_weight r (by norm_num : 1/2 ≤ (1:ℝ)) (Icc 1 ⌊T⌋₊) (Nat.primesLE ⌊T⌋₊) hf
  have hfilter : (Nat.primesLE ⌊T⌋₊).filter Nat.Prime = Nat.primesLE ⌊T⌋₊ := filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  simp only [divisorWeight, Real.rpow_neg_one, ← div_eq_mul_inv, hfilter] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  simpa only [one_div] using mul_le_mul_of_nonneg_left (prime_reciprocals_real T hT) (momentSeriesConst_nonneg r)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.divisor_harmonic_bound := @_root_.OAI.ShortEgyptian.divisor_harmonic_bound
