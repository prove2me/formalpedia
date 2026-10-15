-- Prove2me | solution 1 for OAI.DoublingHilbert.point_dist_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:53:24.575986+00:00
-- url     : https://prove2.me/submissions/294fc697-2291-4792-ab33-cb62b7437501

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Construction.lean:L260-L280
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.point_dist_sq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction

-- ---- from OAI.Geometry.DoublingHilbert.Construction ----
namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

theorem tupleVector_sum_on (w : Tuple) (s : Finset ℕ) (hs : w.support ⊆ s) :
    tupleVector w = ∑ j ∈ s, entryVector w j := by
  classical
  unfold tupleVector
  symm
  calc
    _ = ∑ j ∈ w.support, entryVector w j := by
      symm
      apply Finset.sum_subset hs
      intro j _ hj
      exact entryVector_eq_zero (by simpa using hj)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact entryVector_of_ne_zero (Finsupp.mem_support_iff.mp hj)

theorem inner_entryVector_entryVector {j m : ℕ} (hjm : j ≠ m) (w w' : Tuple) :
    inner ℝ (entryVector w j) (entryVector w' m) = 0 := by
  classical
  unfold entryVector
  split_ifs <;> simp [hjm]

theorem inner_baseVector_levelVector (p : Base) (j i : ℕ) :
    inner ℝ (baseVector p) (levelVector j i) = 0 := by
  simp [baseVector, inner_add_left, lp.inner_single_left, levelVector, lp.single_apply,
    Ne.symm (coordinate_ne_zero j i), Ne.symm (coordinate_ne_one j i)]

theorem inner_baseVector_entryVector (p : Base) (w : Tuple) (j : ℕ) :
    inner ℝ (baseVector p) (entryVector w j) = 0 := by
  classical
  unfold entryVector
  split_ifs <;> simp [inner_baseVector_levelVector]

/-- Finite Pythagoras for pairwise orthogonal vectors. -/
theorem norm_sum_sq_of_inner_eq_zero {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Finset ι) (v : ι → E)
    (hv : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]
  rw [Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j hj hji
    exact hv i hi j hj hji.symm
  · exact fun h => (h hi).elim

/-- Exact orthogonal decomposition of source distances. -/
theorem point_dist_sq (p q : Base) (w w' : Tuple) (s : Finset ℕ)
    (hw : w.support ⊆ s) (hw' : w'.support ⊆ s) :
    dist (point p w) (point q w') ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 +
      ∑ j ∈ s, ‖entryVector w j - entryVector w' j‖ ^ 2 := by
  rw [dist_eq_norm]
  have heq : point p w - point q w' = baseVector (p - q) +
      ∑ j ∈ s, (entryVector w j - entryVector w' j) := by
    rw [Finset.sum_sub_distrib, ← tupleVector_sum_on w s hw, ← tupleVector_sum_on w' s hw',
      ← baseVector_sub]
    simp only [point]
    abel
  rw [heq, norm_add_sq_real]
  have hinner : inner ℝ (baseVector (p - q))
      (∑ j ∈ s, (entryVector w j - entryVector w' j)) = 0 := by
    simp [inner_sum, inner_sub_right, inner_baseVector_entryVector]
  rw [hinner, mul_zero, add_zero, baseVector_norm_sq]
  congr 1
  apply norm_sum_sq_of_inner_eq_zero
  intro i _ j _ hij
  simp [inner_sub_left, inner_sub_right, inner_entryVector_entryVector hij]

end DoublingHilbert

end

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open scoped BigOperators
open Set

theorem solution (p q : Base) (w w' : Tuple) (s : Finset ℕ)
    (hw : w.support ⊆ s) (hw' : w'.support ⊆ s) :
    dist (point p w) (point q w') ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 +
      ∑ j ∈ s, ‖entryVector w j - entryVector w' j‖ ^ 2 := by
  first
    | exact OAI.DoublingHilbert.point_dist_sq p q w w' s hw hw'
    | exact OAI.DoublingHilbert.point_dist_sq
    | (apply OAI.DoublingHilbert.point_dist_sq <;> assumption)
    | (intros; apply OAI.DoublingHilbert.point_dist_sq <;> assumption)
