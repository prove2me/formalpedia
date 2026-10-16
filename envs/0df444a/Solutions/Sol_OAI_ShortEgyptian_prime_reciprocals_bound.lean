-- Prove2me | solution 1 for OAI.ShortEgyptian.prime_reciprocals_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:52:48.317309+00:00
-- url     : https://prove2.me/submissions/747d88e7-054c-48f4-9275-39b321553a78

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/PrimeReciprocals.lean:L83-L104
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.prime_reciprocals_bound. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_prime_reciprocals_dyadic

-- ---- from OAI.NumberTheory.ShortEgyptian.PrimeReciprocals ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem prime_reciprocals_bound (T : ℕ) (hT : 2 ≤ T) :
    ∑ p ∈ Nat.primesLE T, (1 : ℝ) / p ≤
      8 + 4 * Real.log (1 + Real.log T / Real.log 2) := by
  let K := Nat.log 2 T
  have hK : 0 < K := Nat.log_pos (by norm_num) hT
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hpower : (2 : ℝ) ^ K ≤ T := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : T ≠ 0)
  have hlog : (K : ℝ) ≤ Real.log T / Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    simpa [Real.log_pow] using Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ K) hpower
  have hharm := harmonic_le_one_add_log K
  have hlog' : Real.log K ≤ Real.log (1 + Real.log T / Real.log 2) := by
    apply Real.log_le_log (by exact_mod_cast hK)
    linarith
  calc
    _ ≤ ∑ p ∈ Nat.primesLE (2 ^ (K + 1)), (1 : ℝ) / p :=
      sum_le_sum_of_subset_of_nonneg
        (Nat.primesLE_mono (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) T).le)
        (fun _ _ _ => by positivity)
    _ ≤ 4 * (1 + (harmonic K : ℝ)) := prime_reciprocals_dyadic K
    _ ≤ _ := by linarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.prime_reciprocals_bound := @_root_.OAI.ShortEgyptian.prime_reciprocals_bound
