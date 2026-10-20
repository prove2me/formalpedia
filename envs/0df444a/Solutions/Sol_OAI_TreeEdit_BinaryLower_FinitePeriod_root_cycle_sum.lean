-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FinitePeriod.root_cycle_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:38:54.73536+00:00
-- url     : https://prove2.me/submissions/9e2b2c4c-d0e7-4a78-95dd-6afec76b761f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FinitePeriod.lean:L65-L81
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FinitePeriod.root_cycle_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool

-- ---- from OAI.Combinatorics.BinaryEdit.FinitePeriod ----
namespace OAI

/-!
# Short-period detection for the finite-tree obstruction

Complete-period averaging gives the short-period detection estimate in
`prop:finite-lower`.
-/

open scoped BigOperators

namespace TreeEdit.BinaryLower.FinitePeriod

lemma norm_one_sub_sq {z : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - z‖ ^ 2 = 2 - 2 * z.re := by
  rw [Complex.sq_norm, Complex.normSq_sub]
  simp [Complex.normSq_eq_norm_sq, hz]
  ring

/-- Complete nontrivial root-of-unity periods have mean squared displacement
exactly two. Primitivity is unnecessary: any positive period works. -/
lemma root_cycle_sum {z : ℂ} {q : ℕ} (hz : ‖z‖ = 1)
    (hne : z ≠ 1) (hroot : z ^ q = 1) :
    ∑ s ∈ Finset.range q, ‖1 - z ^ (s + 1)‖ ^ 2 = 2 * (q : ℝ) := by
  have hgeom : (∑ s ∈ Finset.range q, z ^ s) = 0 := by
    rw [geom_sum_eq hne, hroot]
    simp
  have hgeom' : (∑ s ∈ Finset.range q, z ^ (s + 1)) = 0 := by
    simp_rw [pow_succ]
    rw [← Finset.sum_mul, hgeom, zero_mul]
  have hre : (∑ s ∈ Finset.range q, (z ^ (s + 1)).re) = 0 := by
    simpa using congrArg Complex.re hgeom'
  simp_rw [norm_one_sub_sq (by simp [norm_pow, hz] : ‖z ^ (_ + 1)‖ = 1)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hre]
  simp
  ring

end TreeEdit.BinaryLower.FinitePeriod

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FinitePeriod
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FinitePeriod.root_cycle_sum := @_root_.OAI.TreeEdit.BinaryLower.FinitePeriod.root_cycle_sum
