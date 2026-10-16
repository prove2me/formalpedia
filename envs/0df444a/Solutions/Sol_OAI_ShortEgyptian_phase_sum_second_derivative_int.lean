-- Prove2me | solution 1 for OAI.ShortEgyptian.phase_sum_second_derivative_int
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:23:47.974715+00:00
-- url     : https://prove2.me/submissions/cad3e54a-3020-43b6-af7c-fca4dc1bd10b

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/IteratedDifferencing.lean:L145-L162
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.phase_sum_second_derivative_int. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Theorems.Thm_OAI_ShortEgyptian_phase_sum_second_derivative_sqrt

-- ---- from OAI.NumberTheory.ShortEgyptian.IteratedDifferencing ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem phase_sum_second_derivative_int (f : ℤ → ℝ) (p q : ℤ) (hpq : p ≤ q)
    {lam A : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hstep : ∀ n ∈ Ico p q,
      lam ≤ (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ∧
      (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ≤ A * lam) :
    ‖∑ n ∈ Icc p q, phase (f n)‖ ≤
      6 * A * (q - p : ℤ) * Real.sqrt lam + 6 / Real.sqrt lam + 6 := by
  have hlen : (q + 1 - p).toNat = (q - p).toNat + 1 := by omega
  have hcast : (((q - p).toNat : ℕ) : ℝ) = (q - p : ℤ) := by
    exact_mod_cast (show ((q - p).toNat : ℤ) = q - p by omega)
  have hh := phase_sum_second_derivative_sqrt (fun n : ℕ => f (p + n))
    (q - p).toNat hlam hlam1 hA (by
      intro n hn
      have hn' : p + (n : ℤ) ∈ Ico p q := mem_Ico.mpr ⟨by omega, by omega⟩
      simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, add_assoc] using hstep (p + n) hn')
  rw [Int.Icc_eq_finset_map, sum_map, hlen]
  simpa only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply, hcast] using hh

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.phase_sum_second_derivative_int := @_root_.OAI.ShortEgyptian.phase_sum_second_derivative_int
