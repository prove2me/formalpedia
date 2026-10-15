-- Prove2me | solution 1 for OAI.ParityWL.testSpan_replacementSum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:39:29.587896+00:00
-- url     : https://prove2.me/submissions/42f9d0b3-5057-4b4a-98e5-398f4cae45f1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Interpolation.lean:L82-L101
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.testSpan_replacementSum. The node keeps its source
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
import Theorems.Thm_OAI_ParityWL_testSpan_reindex
import Theorems.Thm_OAI_ParityWL_testSpan_sumInsert

-- ---- from OAI.Combinatorics.ParityLifts.Interpolation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section FiniteInterpolation

open scoped Classical

end FiniteInterpolation

section RefinementOperators

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

lemma insertNth_comp_succAbove {k : ℕ} {A : Type} (i : Fin (k + 1)) (y : A)
    (x : Fin (k + 1) → A) :
    i.insertNth y (x ∘ i.succAbove) = Function.update x i y :=
  Fin.insertNth_removeNth i y x

lemma testSpan_replacementSum {k t : ℕ} (hkt : k ≤ t) (i : Fin k)
    {f : TuplePair V W k → ℚ} (hf : f ∈ testSpan G H k t) :
    replacementSum i f ∈ testSpan G H k t := by
  cases k with
  | zero => exact i.elim0
  | succ k =>
    have hmem := testSpan_reindex G H hkt i.succAbove
      (testSpan_sumInsert G H (by omega) i hf)
    have he : replacementSum i f = reindexLinear i.succAbove (sumInsertLinear i f) := by
      funext a
      cases a with
      | inl x =>
        change (∑ y : V, f (.inl (Function.update x i y))) =
          ∑ y : V, f (.inl (i.insertNth y (x ∘ i.succAbove)))
        simp only [insertNth_comp_succAbove]
      | inr x =>
        change (∑ y : W, f (.inr (Function.update x i y))) =
          ∑ y : W, f (.inr (i.insertNth y (x ∘ i.succAbove)))
        simp only [insertNth_comp_succAbove]
    rwa [← he] at hmem

end RefinementOperators

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.testSpan_replacementSum := @_root_.OAI.ParityWL.testSpan_replacementSum
