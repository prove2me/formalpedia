-- Prove2me | solution 1 for OAI.ParityWL.atomic_indicator_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:43:39.642277+00:00
-- url     : https://prove2.me/submissions/6287fd50-b1a4-46e9-b5ff-5702394186f5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/ColorSpan.lean:L42-L59
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.atomic_indicator_mem. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra
import Definitions.Def_OAI_Combinatorics_ParityLifts_Interpolation
import Definitions.Def_OAI_Combinatorics_ParityLifts_ColorSpan
import Theorems.Thm_OAI_ParityWL_color_indicator_mem_of_separation
import Theorems.Thm_OAI_ParityWL_edgeTest_count
import Theorems.Thm_OAI_ParityWL_equalityTest_count

-- ---- from OAI.Combinatorics.ParityLifts.ColorSpan ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section ColorSpan

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

lemma boolIndicator_injective : Function.Injective boolIndicator := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolIndicator]

lemma testEval_equality {k t : ℕ} (hkt : k ≤ t) (i j : Fin k) (a : TuplePair V W k) :
    testEval G H (equalityTest hkt i j) a = boolIndicator ((pairAtomic G H a i j).1) := by
  cases a <;> simp [testEval, equalityTest_count, pairAtomic, atomicType, boolIndicator]

lemma testEval_edge {k t : ℕ} (hkt : k ≤ t) (i j : Fin k) (a : TuplePair V W k) :
    testEval G H (edgeTest hkt i j) a = boolIndicator ((pairAtomic G H a i j).2) := by
  cases a <;> simp [testEval, edgeTest_count, pairAtomic, atomicType, boolIndicator]

lemma atomic_indicator_mem {k t : ℕ} (hkt : k ≤ t) (d : AtomicType k) :
    (fun x => if pairAtomic G H x = d then (1 : ℚ) else 0) ∈ testSpan G H k t := by
  refine color_indicator_mem_of_separation (testAlgebra G H k t hkt) (pairAtomic G H) ?_ d
  intro x y hxy
  by_contra! hn
  apply hxy
  funext i j
  apply Prod.ext
  · apply boolIndicator_injective
    rw [← testEval_equality G H hkt i j x, ← testEval_equality G H hkt i j y]
    apply hn _ (testEval_mem G H _)
    intro z w hzw
    rw [testEval_equality, testEval_equality, hzw]
  · apply boolIndicator_injective
    rw [← testEval_edge G H hkt i j x, ← testEval_edge G H hkt i j y]
    apply hn _ (testEval_mem G H _)
    intro z w hzw
    rw [testEval_edge, testEval_edge, hzw]

end ColorSpan

section SpanHistograms

open scoped Classical

variable {V W X Y D : Type} [Fintype V] [Fintype W] [Fintype X] [Fintype Y]
variable (G : SimpleGraph V) (H : SimpleGraph W) {k t : ℕ}
variable (l : X → TuplePair V W k) (r : Y → TuplePair V W k)

end SpanHistograms

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.atomic_indicator_mem := @_root_.OAI.ParityWL.atomic_indicator_mem
