-- Prove2me | solution 1 for OAI.ShortEgyptian.rough_cardFactors_log
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:03:52.85978+00:00
-- url     : https://prove2.me/submissions/936f35dd-24d8-4bf1-88ee-778e6d93dd5c

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/TruncatedDivisors.lean:L34-L49
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.rough_cardFactors_log. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.TruncatedDivisors ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem rough_cardFactors_log {n : ℕ} (hn : n ≠ 0) (z : ℝ) (hz : 0 < z)
    (hrough : ∀ p ∈ n.primeFactorsList, z ≤ p) :
    (ArithmeticFunction.cardFactors n : ℝ) * Real.log z ≤ Real.log n := by
  have hprod : (n.primeFactorsList.map (fun p : ℕ => (p:ℝ))).prod = n := by
    rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList hn]
  have hlog := Real.log_list_prod (l := n.primeFactorsList.map (fun p : ℕ => (p:ℝ))) (by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact_mod_cast (Nat.pos_of_mem_primeFactorsList hp).ne')
  rw [hprod, List.map_map] at hlog
  have hh := List.card_nsmul_le_sum (n.primeFactorsList.map (fun p : ℕ => Real.log (p:ℝ))) (Real.log z) (by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact Real.log_le_log hz (hrough p hp))
  rw [hlog]
  simpa [ArithmeticFunction.cardFactors_apply, List.length_map, nsmul_eq_mul, Function.comp_def] using hh

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.rough_cardFactors_log := @_root_.OAI.ShortEgyptian.rough_cardFactors_log
