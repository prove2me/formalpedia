-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.character_multiplier_average
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:07:23.749803+00:00
-- url     : https://prove2.me/submissions/3046399e-a0d8-47cd-87d7-2bbfb247a86c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean:L304-L323
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.character_multiplier_average. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.SparseActivity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Sparse activity in a finite branching construction

Sparse/dense Fourier-mass estimates for `prop:finite-lower`.
-/

namespace TreeEdit.BinaryLower.TreeDistortion.FiniteMass

open scoped BigOperators
open Classical

/-- Full-period averaging detects a nontrivial character with multiplier two.
Applied to a cyclic coordinate subgroup, this is the source's leaf test. -/
theorem character_multiplier_average {A : Type*} [AddCommGroup A] [Fintype A]
    (χ : AddChar A ℂ) :
    (∑ z : A, ‖1 - χ z‖ ^ 2) / (Fintype.card A : ℝ) =
      if χ = 0 then 0 else 2 := by
  classical
  by_cases hχ : χ = 0
  · simp [hχ]
  · rw [ite_eq_right hχ]
    have hsum : (∑ z : A, χ z) = 0 := AddChar.sum_eq_zero_iff_ne_zero.mpr hχ
    have hre : (∑ z : A, (χ z).re) = 0 := by
      simpa using congrArg Complex.re hsum
    have hpoint : ∀ z : A, ‖1 - χ z‖ ^ 2 = 2 * (1 - (χ z).re) := by
      intro z
      rw [norm_sub_rev, Complex.norm_sub_one_sq_eq_of_norm_eq_one (χ.norm_apply z)]
    simp_rw [hpoint]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    have hcard : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [hre, hcard]

end TreeEdit.BinaryLower.TreeDistortion.FiniteMass

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TreeDistortion OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.character_multiplier_average := @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.character_multiplier_average
