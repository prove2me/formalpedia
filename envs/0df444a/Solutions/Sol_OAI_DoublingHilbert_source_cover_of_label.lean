-- Prove2me | solution 1 for OAI.DoublingHilbert.source_cover_of_label
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:49:49.455159+00:00
-- url     : https://prove2.me/submissions/09ada169-3727-43eb-a11a-9ba2165494ee

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Doubling.lean:L224-L255
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.source_cover_of_label. The node keeps its source
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
import Theorems.Thm_OAI_DoublingHilbert_cover_of_finite_code
import Theorems.Thm_OAI_DoublingHilbert_point_dist_lt_half
import Theorems.Thm_OAI_DoublingHilbert_point_dist_sq

-- ---- from OAI.Geometry.DoublingHilbert.Construction ----
namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

theorem abs_fst_sub_le_dist (p q : Base) (w w' : Tuple) :
    |p.1 - q.1| ≤ dist (point p w) (point q w') := by
  classical
  have hd := point_dist_sq p q w w' (w.support ∪ w'.support)
    Finset.subset_union_left Finset.subset_union_right
  have hsum := Finset.sum_nonneg (s := w.support ∪ w'.support)
    (f := fun j => ‖entryVector w j - entryVector w' j‖ ^ 2) (fun _ _ => sq_nonneg _)
  nlinarith [sq_abs (p.1 - q.1), sq_nonneg (p.2 - q.2),
    dist_nonneg (x := point p w) (y := point q w')]

theorem abs_snd_sub_le_dist (p q : Base) (w w' : Tuple) :
    |p.2 - q.2| ≤ dist (point p w) (point q w') := by
  classical
  have hd := point_dist_sq p q w w' (w.support ∪ w'.support)
    Finset.subset_union_left Finset.subset_union_right
  have hsum := Finset.sum_nonneg (s := w.support ∪ w'.support)
    (f := fun j => ‖entryVector w j - entryVector w' j‖ ^ 2) (fun _ _ => sq_nonneg _)
  nlinarith [sq_abs (p.2 - q.2), sq_nonneg (p.1 - q.1),
    dist_nonneg (x := point p w) (y := point q w')]

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

theorem coordinateCell_mem {c t x : ℝ} (ht : 0 < t) (hx : |x - c| < t) :
    coordinateCell c t x ∈ Finset.Ico (0 : ℤ) 16 := by
  have hxc := abs_lt.mp hx
  have h₀ : 0 ≤ 8 * (x - (c - t)) / t :=
    div_nonneg (by linarith) ht.le
  have h₁ : 8 * (x - (c - t)) / t < 16 := by
    apply (div_lt_iff₀ ht).mpr
    linarith
  rw [Finset.mem_Ico, coordinateCell]
  constructor
  · exact Int.floor_nonneg.mpr h₀
  · exact Int.floor_lt.mpr h₁

theorem abs_sub_lt_of_coordinateCell_eq {c t x y : ℝ} (ht : 0 < t)
    (h : coordinateCell c t x = coordinateCell c t y) : |x - y| < t / 8 := by
  have hx₀ := Int.floor_le (8 * (x - (c - t)) / t)
  have hx₁ := Int.lt_floor_add_one (8 * (x - (c - t)) / t)
  have hy₀ := Int.floor_le (8 * (y - (c - t)) / t)
  have hy₁ := Int.lt_floor_add_one (8 * (y - (c - t)) / t)
  change ⌊8 * (x - (c - t)) / t⌋ = ⌊8 * (y - (c - t)) / t⌋ at h
  rw [← h] at hy₀ hy₁
  have hx₀' := (le_div_iff₀ ht).mp hx₀
  have hx₁' := (div_lt_iff₀ ht).mp hx₁
  have hy₀' := (le_div_iff₀ ht).mp hy₀
  have hy₁' := (div_lt_iff₀ ht).mp hy₁
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end DoublingHilbert

open Set Metric
noncomputable section
namespace DoublingHilbert

end DoublingHilbert

namespace DoublingHilbert
open Set
open scoped BigOperators

theorem source_eq_point (z : constructedSet) : (z : RealL2) = point (sourceBase z) (sourceTuple z) :=
  (Classical.choose_spec (Classical.choose_spec z.prop)).2

theorem sourceBase_fst_dist_le (z z' : constructedSet) :
    |(sourceBase z).1 - (sourceBase z').1| ≤ dist z z' := by
  change _ ≤ dist (z : RealL2) (z' : RealL2)
  rw [source_eq_point z, source_eq_point z']
  exact abs_fst_sub_le_dist _ _ _ _

theorem sourceBase_snd_dist_le (z z' : constructedSet) :
    |(sourceBase z).2 - (sourceBase z').2| ≤ dist z z' := by
  change _ ≤ dist (z : RealL2) (z' : RealL2)
  rw [source_eq_point z, source_eq_point z']
  exact abs_snd_sub_le_dist _ _ _ _

/-- Intrinsic centers for any valid intermediate coordinate coding. -/
theorem source_cover_of_label (x : constructedSet) {t : ℝ} (ht : 0 < t)
    (labels : Finset ℕ) (hcard : labels.card ≤ 300)
    (label : Metric.ball x t → {i // i ∈ labels})
    (hlabel : ∀ y z : Metric.ball x t, label y = label z →
      ∀ j, t / 64 < scale j → sourceTuple y.val j = sourceTuple z.val j) :
    ∃ centers : Finset constructedSet, centers.card ≤ 76800 ∧
      ∀ y : constructedSet, dist y x < t → ∃ c ∈ centers, dist y c < t / 2 := by
  classical
  let cells : Finset ℤ := Finset.Ico 0 16
  let key₁ : Metric.ball x t → {i // i ∈ cells} := fun y =>
    ⟨coordinateCell (sourceBase x).1 t (sourceBase y.val).1,
      coordinateCell_mem ht ((sourceBase_fst_dist_le y.val x).trans_lt y.prop)⟩
  let key₂ : Metric.ball x t → {i // i ∈ cells} := fun y =>
    ⟨coordinateCell (sourceBase x).2 t (sourceBase y.val).2,
      coordinateCell_mem ht ((sourceBase_snd_dist_le y.val x).trans_lt y.prop)⟩
  let code := fun y : Metric.ball x t => (key₁ y, key₂ y, label y)
  obtain ⟨centers, hc, _, hcover⟩ := cover_of_finite_code (Metric.ball x t) code
    (r := t / 2) (by
      intro y z heq
      have h₁ := congrArg (fun v => v.1.val) heq
      have h₂ := congrArg (fun v => v.2.1.val) heq
      have hlabel' := congrArg (fun v => v.2.2) heq
      change dist (y.val : RealL2) (z.val : RealL2) < t / 2
      rw [source_eq_point y.val, source_eq_point z.val]
      exact point_dist_lt_half ht (abs_sub_lt_of_coordinateCell_eq ht h₁)
        (abs_sub_lt_of_coordinateCell_eq ht h₂) (hlabel y z hlabel'))
  refine ⟨centers, ?_, hcover⟩
  have hcells : Fintype.card {i // i ∈ cells} = 16 := by
    simp only [Fintype.card_coe, cells, Int.card_Ico]; decide
  simp only [Fintype.card_prod, hcells, Fintype.card_coe] at hc
  omega

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

theorem solution (x : constructedSet) {t : ℝ} (ht : 0 < t)
    (labels : Finset ℕ) (hcard : labels.card ≤ 300)
    (label : Metric.ball x t → {i // i ∈ labels})
    (hlabel : ∀ y z : Metric.ball x t, label y = label z →
      ∀ j, t / 64 < scale j → sourceTuple y.val j = sourceTuple z.val j) :
    ∃ centers : Finset constructedSet, centers.card ≤ 76800 ∧
      ∀ y : constructedSet, dist y x < t → ∃ c ∈ centers, dist y c < t / 2 := by
  first
    | exact OAI.DoublingHilbert.source_cover_of_label x ht labels hcard label hlabel
    | exact OAI.DoublingHilbert.source_cover_of_label
    | (apply OAI.DoublingHilbert.source_cover_of_label <;> assumption)
    | (intros; apply OAI.DoublingHilbert.source_cover_of_label <;> assumption)
