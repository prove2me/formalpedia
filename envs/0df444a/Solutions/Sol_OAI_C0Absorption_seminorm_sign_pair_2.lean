-- Prove2me | solution 2 for OAI.C0Absorption.seminorm_sign_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:36:22.783985+00:00
-- url     : https://prove2.me/submissions/dd6505cd-76d0-470e-975d-ef7a1fab8e03

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Signs.lean:L118-L134
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.seminorm_sign_pair. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs

-- ---- from OAI.Analysis.C0Absorption.Signs ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section Signs

theorem signed_sum_sub_flip {X : Type*} [AddCommGroup X] [Module ℝ X]
    {n : ℕ} (m : Fin n → X) (ε : Fin n → Bool) (i : Fin n) :
    (∑ j, realSign (ε j) • m j) - (∑ j, realSign (flipSign i ε j) • m j) =
      (2 * realSign (ε i)) • m i := by
  classical
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp [flipSign, two_mul, add_smul]
  · intro j hj hji
    simp [flipSign, hji]
  · simp

theorem seminorm_sign_pair {X : Type*} [AddCommGroup X] [Module ℝ X]
    (q : Seminorm ℝ X) {n : ℕ} (m : Fin n → X) (ε : Fin n → Bool) (i : Fin n) :
    2 * (q (m i)) ^ 2 ≤
      (q (∑ j, realSign (ε j) • m j)) ^ 2 +
      (q (∑ j, realSign (flipSign i ε j) • m j)) ^ 2 := by
  have heq : q ((∑ j, realSign (ε j) • m j) -
      (∑ j, realSign (flipSign i ε j) • m j)) = 2 * q (m i) := by
    rw [signed_sum_sub_flip, map_smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_realSign]
    norm_num
  have ht := map_add_le_add q
    (∑ j, realSign (ε j) • m j) (-(∑ j, realSign (flipSign i ε j) • m j))
  rw [← sub_eq_add_neg, heq, map_neg_eq_map] at ht
  have hp := apply_nonneg q (m i)
  have ha := apply_nonneg q (∑ j, realSign (ε j) • m j)
  have hb := apply_nonneg q (∑ j, realSign (flipSign i ε j) • m j)
  nlinarith [sq_nonneg (q (∑ j, realSign (ε j) • m j) -
    q (∑ j, realSign (flipSign i ε j) • m j))]

end Signs

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset


theorem solution : type_of% @_root_.OAI.C0Absorption.seminorm_sign_pair := @_root_.OAI.C0Absorption.seminorm_sign_pair
