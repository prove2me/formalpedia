-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.CutAggregation.aggregate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:28:37.631978+00:00
-- url     : https://prove2.me/submissions/a6be7f79-c2c5-448e-8255-1156f44276bc

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CutAggregation.lean:L42-L73
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.CutAggregation.aggregate. The node keeps its source
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

lemma summable_L1_abs_sub (f g : TreeEdit.RealL1) :
    Summable (fun n : ℕ => |f n - g n|) := by
  simpa only [ENNReal.toReal_one, Real.rpow_one, lp.coeFn_sub, Pi.sub_apply,
    Real.norm_eq_abs] using (lp.memℓp (f - g)).summable (by simp)

lemma norm_L1_sub (f g : TreeEdit.RealL1) :
    ‖f - g‖ = ∑' n : ℕ, |f n - g n| := by
  simpa only [ENNReal.toReal_one, Real.rpow_one, one_div_one, lp.coeFn_sub,
    Pi.sub_apply, Real.norm_eq_abs] using lp.norm_eq_tsum_rpow (by simp) (f - g)

/-- A nontrivial cut weight is dominated by any coordinate distance across
that cut. This makes the countable grouping legitimate without a finite
support assumption on the image in ℓ₁. -/
lemma scalar_weight_le {S : Type u} {C : Type v} [Fintype C]
    (f : S → ℝ) (U : C → S → ℝ) (a : C → ℝ)
    (ha : ∀ c, 0 ≤ a c)
    (hrep : ∀ x y, |f x - f y| = ∑ c, a c * |U c x - U c y|)
    (c : C) (x y : S) (hxy : |U c x - U c y| = 1) :
    a c ≤ |f x - f y| := by
  classical
  rw [hrep]
  calc
    a c = a c * |U c x - U c y| := by rw [hxy, mul_one]
    _ ≤ ∑ k, a k * |U k x - U k y| :=
      Finset.single_le_sum (fun k _ => mul_nonneg (ha k) (abs_nonneg (U k x - U k y)))
        (Finset.mem_univ c)

/-- Countably many scalar decompositions combine into an actual finite cut
representation of a map into the full absolutely summable sequence space.
Null cuts are permitted, but their coordinate weights must vanish. -/
theorem aggregate {S : Type u} {C : Type v} [Fintype C]
    (F : S → TreeEdit.RealL1) (U : C → S → ℝ) (a : ℕ → C → ℝ)
    (ha : ∀ n c, 0 ≤ a n c)
    (hcut : ∀ c, (∀ n, a n c = 0) ∨ ∃ x y, |U c x - U c y| = 1)
    (hrep : ∀ n x y,
      |F x n - F y n| = ∑ c, a n c * |U c x - U c y|) :
    ∃ A : C → ℝ, (∀ c, 0 ≤ A c) ∧
      (∀ c, A c = ∑' n, a n c) ∧
      (∀ x y, ‖F x - F y‖ = ∑ c, A c * |U c x - U c y|) := by
  classical
  have hs : ∀ c, Summable (fun n => a n c) := by
    intro c
    rcases hcut c with hz | ⟨x, y, hxy⟩
    · simpa only [hz] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    · exact Summable.of_nonneg_of_le (fun n => ha n c)
        (fun n => scalar_weight_le (fun x => F x n) U (a n) (ha n) (hrep n) c x y hxy)
        (summable_L1_abs_sub (F x) (F y))
  refine ⟨fun c => ∑' n, a n c, ?_, fun _ => rfl, ?_⟩
  · intro c
    exact tsum_nonneg (fun n => ha n c)
  · intro x y
    rw [norm_L1_sub]
    simp_rw [hrep]
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro c _
      exact (hs c).tsum_mul_right _
    · intro c _
      exact (hs c).mul_right _

end TreeEdit.BinaryLower.CutAggregation

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.CutAggregation


theorem solution.{u,v} : type_of% @_root_.OAI.TreeEdit.BinaryLower.CutAggregation.aggregate.{u,v} := @_root_.OAI.TreeEdit.BinaryLower.CutAggregation.aggregate.{u,v}
