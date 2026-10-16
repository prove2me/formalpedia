-- Prove2me | solution 1 for OAI.ShortEgyptian.finite_parseval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:02:16.841551+00:00
-- url     : https://prove2.me/submissions/e1823138-8154-4827-95aa-15dc927a628e

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/FiniteFourier.lean:L21-L44
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.finite_parseval. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic

-- ---- from OAI.NumberTheory.ShortEgyptian.FiniteFourier ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uG

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem additive_orthogonality {q : ℕ} [NeZero q] (t : ZMod q) :
    (∑ x : ZMod q, ZMod.stdAddChar (t * x)) = if t = 0 then (q : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q ht)

theorem finite_parseval {q : ℕ} [NeZero q] (β : ZMod q → ℂ) :
    ∑ x : ZMod q, ‖∑ y : ZMod q, β y * ZMod.stdAddChar (x * y)‖ ^ 2 =
      (q : ℝ) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq]
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    ← AddChar.map_neg_eq_conj]
  have hterm (x y z : ZMod q) :
      β y * ZMod.stdAddChar (x * y) *
        ((starRingEnd ℂ) (β z) * ZMod.stdAddChar (-(x * z))) =
      (β y * (starRingEnd ℂ) (β z)) * ZMod.stdAddChar ((y - z) * x) := by
    rw [show (y - z) * x = x * y + -(x * z) by ring, AddChar.map_add_eq_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun y _ => Finset.sum_comm))
  simp only [← Finset.mul_sum, additive_orthogonality, sub_eq_zero]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.finite_parseval := @_root_.OAI.ShortEgyptian.finite_parseval
