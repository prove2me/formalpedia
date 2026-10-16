-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.Numerical.inv_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:19:35.113426+00:00
-- url     : https://prove2.me/submissions/2bb1f600-bb60-44f2-85f9-ca42dfc8ebaa

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Numerical.lean:L154-L168
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.Numerical.inv_scale. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical

-- ---- from OAI.Combinatorics.CliqueFree.Numerical ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace Numerical

end Numerical

end CliqueFreeIndependence

open Filter
namespace CliqueFreeIndependence.Numerical

lemma scale_ge {X : ℝ} (hX : 1 ≤ X) (n : ℕ) : X ≤ scale X n := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 1 ≤ scale X n := hX.trans ih
    dsimp [scale]
    nlinarith

lemma inv_scale {X : ℝ} (hX : 2 ≤ X) (n : ℕ) :
    1 / scale X n ≤ (1/2 : ℝ)^n * (1/X) := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    have ht : 2 ≤ scale X n := hX.trans (scale_ge (by linarith) n)
    have ht0 : 0 < scale X n := by linarith
    have he : 1 / (scale X n)^2 ≤ (1/2) * (1 / scale X n) := by
      apply (div_le_iff₀ (pow_pos ht0 2)).2
      field_simp
      nlinarith
    calc
      _ ≤ (1/2) * (1 / scale X n) := he
      _ ≤ (1/2) * ((1/2 : ℝ)^n * (1/X)) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

end CliqueFreeIndependence.Numerical

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.Numerical
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Filter


theorem solution : type_of% @_root_.OAI.CliqueFreeIndependence.Numerical.inv_scale := @_root_.OAI.CliqueFreeIndependence.Numerical.inv_scale
