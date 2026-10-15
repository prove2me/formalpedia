-- Prove2me | solution 1 for OAI.CompactBanach.norm_map_point_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:19:58.999763+00:00
-- url     : https://prove2.me/submissions/cd4d78f8-f331-41e1-8983-b79efacdc7eb

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/SparseCoordinates.lean:L47-L89
-- (upload_full_project.md Phase 4): solution for node OAI.CompactBanach.norm_map_point_sub_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Theorems.Thm_OAI_DoublingHilbert_tupleVector_sum_on

-- ---- from OAI.Geometry.DoublingHilbert.Construction ----
namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

theorem scale_add (i j : ℕ) : scale (i + j) = scale i * (1000 : ℝ)⁻¹ ^ j := by
  simp only [scale]
  rw [show i + j + 1 = (i + 1) + j by omega, pow_add]

end DoublingHilbert

end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.SparseCoordinates ----
namespace OAI

open Set Metric
noncomputable section
namespace CompactBanach
open DoublingHilbert

theorem sum_scale_le {s : Finset ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ j ∈ s, scale j ≤ R) : ∑ j ∈ s, scale j ≤ 2 * R := by
  classical
  by_cases hse : s.Nonempty
  · let m := s.min' hse
    have hm : m ∈ s := s.min'_mem hse
    have hmj (j : ℕ) (hj : j ∈ s) : m ≤ j := s.min'_le j hj
    have hgeom := (summable_geometric_of_abs_lt_one (r := (1000 : ℝ)⁻¹) (by norm_num)).sum_le_tsum
      (s.image (fun j => j - m)) (fun _ _ => by positivity)
    rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1000 : ℝ)⁻¹| < 1)] at hgeom
    have himage : (∑ j ∈ s.image (fun j => j - m), (1000 : ℝ)⁻¹ ^ j) =
        ∑ j ∈ s, (1000 : ℝ)⁻¹ ^ (j - m) := by
      apply Finset.sum_image
      intro i hi j hj he
      dsimp at he
      have := hmj i hi
      have := hmj j hj
      omega
    rw [himage] at hgeom
    have heq : (∑ j ∈ s, scale j) = scale m *
        ∑ j ∈ s, (1000 : ℝ)⁻¹ ^ (j - m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : m + (j - m) = j := Nat.add_sub_of_le (hmj j hj)
      conv_lhs => rw [← hj', scale_add]
    rw [heq]
    calc
      _ ≤ scale m * (1 - (1000 : ℝ)⁻¹)⁻¹ :=
        mul_le_mul_of_nonneg_left hgeom (scale_pos m).le
      _ ≤ 2 * scale m := by nlinarith [scale_pos m]
      _ ≤ 2 * R := by linarith [hs m hm]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hse, Finset.sum_empty]
    positivity

                                                                   
theorem norm_map_point_sub_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (T : RealL2 →ₗ[ℝ] B) (hT : ∀ i a, ‖T (lp.single 2 i a)‖ ≤ |a|)
    (p q : Base) (w w' : Tuple) {R : ℝ} (hR : 0 ≤ R)
    (hf : |p.1 - q.1| ≤ R) (hs : |p.2 - q.2| ≤ R)
    (hw : ∀ j, w j ≠ w' j → scale j ≤ R) :
    ‖T (point p w - point q w')‖ ≤ 6 * R := by
  classical
  let s := w.support ∪ w'.support
  let d := s.filter fun j => w j ≠ w' j
  have heq : point p w - point q w' = baseVector (p - q) +
      ∑ j ∈ d, (entryVector w j - entryVector w' j) := by
    have hsum : (∑ j ∈ d, (entryVector w j - entryVector w' j)) =
        ∑ j ∈ s, (entryVector w j - entryVector w' j) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hnot
      have he : w j = w' j := by simpa [d, hj] using hnot
      simp [entryVector, he]
    rw [hsum, Finset.sum_sub_distrib,
      ← tupleVector_sum_on w s Finset.subset_union_left,
      ← tupleVector_sum_on w' s Finset.subset_union_right, ← baseVector_sub]
    simp only [point]
    abel
  have hb : ‖T (baseVector (p - q))‖ ≤ 2 * R := by
    simp only [baseVector, map_add, Prod.fst_sub, Prod.snd_sub]
    exact (norm_add_le _ _).trans (by linarith [hT 0 (p.1 - q.1), hT 1 (p.2 - q.2)])
  have he (u : Tuple) (j : ℕ) : ‖T (entryVector u j)‖ ≤ scale j := by
    by_cases hu : u j = 0
    · simp [hu, (scale_pos j).le]
    · simpa only [entryVector_of_ne_zero hu, levelVector, abs_of_pos (scale_pos j)] using
        hT (coordinate j (u j - 1)) (scale j)
  have hd : ‖T (∑ j ∈ d, (entryVector w j - entryVector w' j))‖ ≤ 4 * R := by
    rw [map_sum]
    calc
      _ ≤ ∑ j ∈ d, ‖T (entryVector w j - entryVector w' j)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ d, 2 * scale j := Finset.sum_le_sum fun j _ => by
        rw [map_sub]
        exact (norm_sub_le _ _).trans (by linarith [he w j, he w' j])
      _ = 2 * ∑ j ∈ d, scale j := by rw [Finset.mul_sum]
      _ ≤ 4 * R := by
        have ht := sum_scale_le (s := d) hR (fun j hj => hw j (Finset.mem_filter.mp hj).2)
        linarith
  rw [heq, map_add]
  exact (norm_add_le _ _).trans (by linarith)

end CompactBanach
end

end OAI

-- ---- platform node ----
open OAI OAI.CompactBanach
open Set Metric
open DoublingHilbert


theorem solution : type_of% @_root_.OAI.CompactBanach.norm_map_point_sub_le := @_root_.OAI.CompactBanach.norm_map_point_sub_le
