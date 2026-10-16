-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.Numerical.growth_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:16:50.382223+00:00
-- url     : https://prove2.me/submissions/d417567b-1665-4bcf-9212-fa21ce64b1df

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Numerical.lean:L58-L75
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.Numerical.growth_factor_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Theorems.Thm_OAI_CliqueFreeIndependence_Numerical_log_bounds

-- ---- from OAI.Combinatorics.CliqueFree.Numerical ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace Numerical

lemma pow_six_le_exp {x : ℝ} (hx : 32 ≤ x) : x ^ 6 ≤ Real.exp x := by
  have hx0 : 0 < x := by linarith
  have hlog := log_bounds hx
  calc
    _ = Real.exp (6 * Real.log x) := by
      have hp : Real.log (x ^ 6) = 6 * Real.log x := by simp only [Real.log_pow, Nat.cast_ofNat]
      rw [← hp, Real.exp_log (pow_pos hx0 6)]
    _ ≤ _ := Real.exp_le_exp.2 (by linarith)

lemma growth_factor_le {x : ℝ} (hx : 32 ≤ x) :
    1 + Real.exp x / threshold x ≤ Real.exp (4 * x) := by
  have hx0 : 0 ≤ x := by linarith
  have he1 : 1 ≤ Real.exp x := Real.one_le_exp_iff.2 hx0
  have he2 : 2 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hp3 : 1 ≤ Real.exp x ^ 3 := one_le_pow₀ he1
  have hid : Real.exp x / threshold x = Real.exp x * Real.exp x * x ^ 6 := by
    unfold threshold
    simp only [div_div_eq_mul_div, div_one]
    ring
  rw [hid, show 4 * x = (4 : ℕ) * x by norm_num, Real.exp_nat_mul]
  calc
    _ ≤ 1 + Real.exp x * Real.exp x * Real.exp x :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_six_le_exp hx) (by positivity))
    _ = 1 + Real.exp x ^ 3 := by ring
    _ ≤ 2 * Real.exp x ^ 3 := by linarith
    _ ≤ Real.exp x * Real.exp x ^ 3 := mul_le_mul_of_nonneg_right he2 (by positivity)
    _ = _ := by ring

end Numerical

end CliqueFreeIndependence

open Filter
namespace CliqueFreeIndependence.Numerical

end CliqueFreeIndependence.Numerical

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.Numerical
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.CliqueFreeIndependence.Numerical.growth_factor_le := @_root_.OAI.CliqueFreeIndependence.Numerical.growth_factor_le
