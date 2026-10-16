-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteEntropy.relTerm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:41:13.12941+00:00
-- url     : https://prove2.me/submissions/f31f93bc-f56f-473b-89ba-b245e4a90ad3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteEntropy.lean:L32-L45
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteEntropy.relTerm_nonneg. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy

-- ---- from OAI.Combinatorics.CliqueFree.FiniteEntropy ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteEntropy

variable {I : Type u} [Fintype I]

lemma relTerm_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 < p → 0 < q) : 0 ≤ p * Real.log (p / q) - p + q := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp, hq]
  have hq' := hs hp
  have h := Real.log_le_sub_one_of_pos (div_pos hq' hp)
  have hl : Real.log (q / p) = -Real.log (p / q) := by
    rw [Real.log_div hq'.ne' hp.ne', Real.log_div hp.ne' hq'.ne']
    ring
  rw [hl] at h
  have hm := mul_le_mul_of_nonneg_left h hp.le
  have hc : p * (q / p - 1) = q - p := by field_simp
  rw [hc] at hm
  linarith

variable {J : Type v} [Fintype J]

end FiniteEntropy

end CliqueFreeIndependence

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteEntropy
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteEntropy.relTerm_nonneg := @_root_.OAI.CliqueFreeIndependence.FiniteEntropy.relTerm_nonneg
