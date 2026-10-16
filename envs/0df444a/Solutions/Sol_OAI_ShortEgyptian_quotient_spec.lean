-- Prove2me | solution 1 for OAI.ShortEgyptian.quotient_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:55:50.705984+00:00
-- url     : https://prove2.me/submissions/23db6eb1-57da-47ea-96d1-b488ef5184f7

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/Basic.lean:L26-L39
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.quotient_spec. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic

-- ---- from OAI.NumberTheory.ShortEgyptian.Basic ----
namespace OAI

namespace ShortEgyptian

theorem quotient_spec {v u : ℕ} (hv : 0 < v) (hu : 0 < u) :
    0 < quotient v u ∧ v ≤ u * quotient v u ∧
      u * quotient v u < v + u := by
  have hvq : (0 : ℚ) < v := by exact_mod_cast hv
  have huq : (0 : ℚ) < u := by exact_mod_cast hu
  have hlo := (div_le_iff₀ huq).mp (Nat.le_ceil ((v : ℚ) / u))
  have hhi := Nat.ceil_lt_add_one (le_of_lt (div_pos hvq huq))
  have hhi' := mul_lt_mul_of_pos_right hhi huq
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt huq), one_mul] at hhi'
  refine ⟨Nat.ceil_pos.mpr (div_pos hvq huq), ?_, ?_⟩
  · change v ≤ u * ⌈(v : ℚ) / u⌉₊
    exact_mod_cast (show (v : ℚ) ≤ u * (⌈(v : ℚ) / u⌉₊ : ℚ) by nlinarith [hlo])
  · change u * ⌈(v : ℚ) / u⌉₊ < v + u
    exact_mod_cast (show (u : ℚ) * (⌈(v : ℚ) / u⌉₊ : ℚ) < v + u by nlinarith [hhi'])

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian


theorem solution : type_of% @_root_.OAI.ShortEgyptian.quotient_spec := @_root_.OAI.ShortEgyptian.quotient_spec
