-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_detection_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:01:42.522225+00:00
-- url     : https://prove2.me/submissions/6f819ac5-8e1c-49fc-98c5-8b7d0ce0190d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean:L99-L118
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_detection_bound. The node keeps its source
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
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Sparse activity in a finite branching construction

Sparse/dense Fourier-mass estimates for `prop:finite-lower`.
-/

namespace TreeEdit.BinaryLower.TreeDistortion.FiniteMass

open scoped BigOperators
open Classical

/-- A nonnegative detector that accumulates at least one unit on every bad
frequency bounds the total Fourier weight of those frequencies. -/
theorem weighted_detection_bound {ι σ : Type*} [Fintype ι] [Fintype σ]
    (H : ι → ℝ) (a : σ → ι → ℝ) (bad : ι → Prop)
    (hH : ∀ i, 0 ≤ H i) (ha : ∀ s i, 0 ≤ a s i)
    (hdetect : ∀ i, bad i → 1 ≤ ∑ s, a s i) :
    (∑ i, if bad i then H i else 0) ≤ ∑ s, ∑ i, a s i * H i := by
  classical
  have hpoint : ∀ i, (if bad i then H i else 0) ≤ ∑ s, a s i * H i := by
    intro i
    rw [← Finset.sum_mul]
    by_cases hi : bad i
    · simp only [ite_eq_left hi]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hdetect i hi) (hH i)
    · simp only [ite_eq_right hi]
      exact mul_nonneg (Finset.sum_nonneg (fun s _ => ha s i)) (hH i)
  calc
    (∑ i, if bad i then H i else 0) ≤ ∑ i, ∑ s, a s i * H i :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = ∑ s, ∑ i, a s i * H i := Finset.sum_comm

end TreeEdit.BinaryLower.TreeDistortion.FiniteMass

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TreeDistortion OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_detection_bound := @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_detection_bound
