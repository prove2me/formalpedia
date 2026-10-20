-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:03:17.993674+00:00
-- url     : https://prove2.me/submissions/3ec62a7e-027d-4f42-afad-7927031a5b35

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SparseActivity.lean:L120-L143
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_union_bound. The node keeps its source
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

/-- Union bound for nonnegative Fourier mass. Overlap between bad-node tests
can only increase the sum on the right. -/
theorem weighted_union_bound {ι ν : Type*} [Fintype ι] [Fintype ν]
    (H : ι → ℝ) (bad : ν → ι → Prop) (hH : ∀ i, 0 ≤ H i) :
    (∑ i, if ∃ v, bad v i then H i else 0) ≤
      ∑ v, ∑ i, if bad v i then H i else 0 := by
  classical
  have hpoint : ∀ i, (if ∃ v, bad v i then H i else 0) ≤
      ∑ v, if bad v i then H i else 0 := by
    intro i
    by_cases hi : ∃ v, bad v i
    · obtain ⟨v, hv⟩ := hi
      rw [ite_eq_left (show ∃ v, bad v i from ⟨v, hv⟩)]
      calc
        H i = (if bad v i then H i else 0) := by rw [ite_eq_left hv]
        _ ≤ ∑ w, if bad w i then H i else 0 :=
          Finset.single_le_sum (f := fun w => if bad w i then H i else 0) (fun w _ => by split_ifs; exact hH i; exact le_refl 0) (Finset.mem_univ v)
    · simp only [ite_eq_right hi]
      exact Finset.sum_nonneg (fun v _ => by split_ifs; exact hH i; exact le_refl 0)
  calc
    (∑ i, if ∃ v, bad v i then H i else 0) ≤
        ∑ i, ∑ v, if bad v i then H i else 0 :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = ∑ v, ∑ i, if bad v i then H i else 0 := Finset.sum_comm

end TreeEdit.BinaryLower.TreeDistortion.FiniteMass

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TreeDistortion OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_union_bound := @_root_.OAI.TreeEdit.BinaryLower.TreeDistortion.FiniteMass.weighted_union_bound
