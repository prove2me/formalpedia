-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.CutAggregation.cut_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:30:16.91599+00:00
-- url     : https://prove2.me/submissions/ade6d1df-5a48-4d81-930e-6821dce423fd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CutAggregation.lean:L75-L115
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.CutAggregation.cut_mass_bound. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.CutAggregation ----
namespace OAI

/-! Countable-coordinate aggregation in the finite cut representation. -/

noncomputable section

namespace TreeEdit.BinaryLower.CutAggregation

universe u v

/-- Every nontrivial cut separates two ordered pairs. Hence the finite total
cut mass is bounded by the sum over unordered pairs, written as one half of
the ordered-pair sum (diagonal terms vanish automatically). -/
theorem cut_mass_bound {S : Type u} {C : Type v} [Fintype S] [Fintype C]
    (F : S → TreeEdit.RealL1) (U : C → S → ℝ) (A : C → ℝ)
    (hA : ∀ c, 0 ≤ A c)
    (hcut : ∀ c, A c = 0 ∨ ∃ x y, |U c x - U c y| = 1)
    (hrep : ∀ x y, ‖F x - F y‖ = ∑ c, A c * |U c x - U c y|) :
    ∑ c, A c ≤ (∑ p : S × S, ‖F p.1 - F p.2‖) / 2 := by
  classical
  have hc : ∀ c, 2 * A c ≤ ∑ p : S × S, A c * |U c p.1 - U c p.2| := by
    intro c
    rcases hcut c with hz | ⟨x, y, hxy⟩
    · simp [hz]
    · have hne : x ≠ y := by
        intro h
        subst y
        simp at hxy
      have hp : (x, y) ≠ (y, x) := by
        intro h
        exact hne (congrArg Prod.fst h)
      calc
        2 * A c = ∑ p ∈ ({(x, y), (y, x)} : Finset (S × S)),
            A c * |U c p.1 - U c p.2| := by
          simp only [Finset.sum_insert, Finset.mem_singleton, hp, not_false_eq_true,
            Finset.sum_singleton]
          rw [hxy, abs_sub_comm (U c y) (U c x), hxy]
          ring
        _ ≤ ∑ p : S × S, A c * |U c p.1 - U c p.2| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro p _ _
          exact mul_nonneg (hA c) (abs_nonneg _)
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hc c)
  rw [← Finset.mul_sum, Finset.sum_comm] at hsum
  have heq : (∑ p : S × S, ∑ c, A c * |U c p.1 - U c p.2|) =
      ∑ p : S × S, ‖F p.1 - F p.2‖ := by
    apply Finset.sum_congr rfl
    intro p _
    exact (hrep p.1 p.2).symm
  rw [heq] at hsum
  linarith

end TreeEdit.BinaryLower.CutAggregation

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.CutAggregation


theorem solution.{u,v} : type_of% @_root_.OAI.TreeEdit.BinaryLower.CutAggregation.cut_mass_bound.{u,v} := @_root_.OAI.TreeEdit.BinaryLower.CutAggregation.cut_mass_bound.{u,v}
