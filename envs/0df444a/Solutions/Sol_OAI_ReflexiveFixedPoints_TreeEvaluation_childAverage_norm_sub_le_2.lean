-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.childAverage_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:12:44.569553+00:00
-- url     : https://prove2.me/submissions/4d298a53-2342-4718-9ea3-01369e218bbe

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/TreeEvaluation.lean:L86-L103
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.childAverage_norm_sub_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_WeightedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeEvaluation

-- ---- from OAI.Analysis.Nonexpansive.TreeEvaluation ----
namespace OAI

/-!
# Actual nonlinear evaluation on a weighted ordered tree

The maps act on the literal subtype of a convex subset of a real normed
space. A cutoff value is an output: its own node map is not applied again.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TreeEvaluation

variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- A finite weighted average has the expected weighted sensitivity. -/
theorem childAverage_norm_sub_le (k : ℕ) (H H' : T.Node (k + 1) → K)
    (p : T.Node k) :
    ‖(E.childAverage k H p : X) - E.childAverage k H' p‖ ≤
      ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - H' c‖ := by
  classical
  rw [E.childAverage_val, E.childAverage_val, ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  calc
    ‖∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c • ((H c : X) - H' c)‖ ≤
        ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
          ‖W.weight k c • ((H c : X) - H' c)‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (W.weight_pos k c)]

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.childAverage_norm_sub_le.{u} := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.childAverage_norm_sub_le.{u}
