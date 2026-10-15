-- Prove2me | solution 1 for OAI.DoublingHilbert.point_dist_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:48:12.115913+00:00
-- url     : https://prove2.me/submissions/7ef5aa19-6eda-409f-9311-fcb1fca0e90b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Doubling.lean:L171-L195
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.point_dist_lt_half. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Theorems.Thm_OAI_DoublingHilbert_point_dist_sq
import Theorems.Thm_OAI_DoublingHilbert_sum_scale_sq_le

-- ---- from OAI.Geometry.DoublingHilbert.Construction ----
namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

theorem norm_levelVector_sub_sq (j i h : ℕ) (hih : i ≠ h) :
    ‖levelVector j i - levelVector j h‖ ^ 2 = 2 * (scale j) ^ 2 := by
  rw [norm_sub_sq_real]
  simp [hih]
  ring

theorem norm_entryVector_sub_sq_le (w w' : Tuple) (j : ℕ) :
    ‖entryVector w j - entryVector w' j‖ ^ 2 ≤ 2 * (scale j) ^ 2 := by
  by_cases hw : w j = 0
  · by_cases hw' : w' j = 0
    · simp [hw, hw', sq_nonneg]
    · simp only [entryVector_eq_zero hw, entryVector_of_ne_zero hw', zero_sub,
        norm_neg, norm_levelVector]
      nlinarith [sq_nonneg (scale j)]
  · by_cases hw' : w' j = 0
    · simp only [entryVector_eq_zero hw', entryVector_of_ne_zero hw, sub_zero, norm_levelVector]
      nlinarith [sq_nonneg (scale j)]
    · rw [entryVector_of_ne_zero hw, entryVector_of_ne_zero hw']
      by_cases heq : w j - 1 = w' j - 1
      · simp [heq, sq_nonneg]
      · exact (norm_levelVector_sub_sq _ _ _ heq).le

/-- A uniform squared-distance bound for the finite-coordinate fine tail. -/
theorem fine_tail_le (w w' : Tuple) (s : Finset ℕ) {t : ℝ} (ht : 0 < t)
    (hs : ∀ j ∈ s, scale j ≤ t / 64) :
    ∑ j ∈ s, ‖entryVector w j - entryVector w' j‖ ^ 2 ≤ t ^ 2 / 1024 := by
  calc
    _ ≤ ∑ j ∈ s, 2 * scale j ^ 2 := Finset.sum_le_sum fun j _ => norm_entryVector_sub_sq_le w w' j
    _ = 2 * ∑ j ∈ s, scale j ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * (2 * (t / 64) ^ 2) := by
      gcongr
      exact sum_scale_sq_le (by positivity) hs
    _ = t ^ 2 / 1024 := by ring

end DoublingHilbert

end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.Doubling ----
namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators Topology

/-! Intrinsic doubling of the same fixed Hilbert subset. -/

open Set
noncomputable section
namespace DoublingHilbert

end DoublingHilbert

open Set Metric
noncomputable section
namespace DoublingHilbert

end DoublingHilbert

namespace DoublingHilbert
open Set
open scoped BigOperators

/-- Same coarse and intermediate coordinates, and one base cell, force small diameter. -/
theorem point_dist_lt_half {p q : Base} {w w' : Tuple} {t : ℝ} (ht : 0 < t)
    (hx : |p.1 - q.1| < t / 8) (hy : |p.2 - q.2| < t / 8)
    (hlarge : ∀ j, t / 64 < scale j → w j = w' j) :
    dist (point p w) (point q w') < t / 2 := by
  classical
  let s := w.support ∪ w'.support
  let small := s.filter (fun j => scale j ≤ t / 64)
  have hs : ∀ j ∈ small, scale j ≤ t / 64 := fun j hj => (Finset.mem_filter.mp hj).2
  have hsum : (∑ j ∈ s, ‖entryVector w j - entryVector w' j‖ ^ 2) =
      ∑ j ∈ small, ‖entryVector w j - entryVector w' j‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hjs
    have hgt : t / 64 < scale j := by
      simpa only [small, Finset.mem_filter, hj, true_and, not_le] using hjs
    simp [entryVector, hlarge j hgt]
  have hd := point_dist_sq p q w w' s Finset.subset_union_left Finset.subset_union_right
  rw [hsum] at hd
  have htail := fine_tail_le w w' small ht hs
  have hx' : (p.1 - q.1)^2 < (t / 8)^2 := by
    nlinarith [sq_abs (p.1 - q.1), abs_nonneg (p.1 - q.1)]
  have hy' : (p.2 - q.2)^2 < (t / 8)^2 := by
    nlinarith [sq_abs (p.2 - q.2), abs_nonneg (p.2 - q.2)]
  nlinarith [dist_nonneg (x := point p w) (y := point q w'), sq_pos_of_pos ht]

end DoublingHilbert

end
end

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Set
open Set Metric
open Set
open scoped BigOperators

theorem solution {p q : Base} {w w' : Tuple} {t : ℝ} (ht : 0 < t)
    (hx : |p.1 - q.1| < t / 8) (hy : |p.2 - q.2| < t / 8)
    (hlarge : ∀ j, t / 64 < scale j → w j = w' j) :
    dist (point p w) (point q w') < t / 2 := by
  first
    | exact OAI.DoublingHilbert.point_dist_lt_half ht hx hy hlarge
    | exact OAI.DoublingHilbert.point_dist_lt_half
    | (apply OAI.DoublingHilbert.point_dist_lt_half <;> assumption)
    | (intros; apply OAI.DoublingHilbert.point_dist_lt_half <;> assumption)
