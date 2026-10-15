-- Prove2me | solution 1 for OAI.CompactBanach.finite_placement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:25:05.189212+00:00
-- url     : https://prove2.me/submissions/31a73721-ae64-4b25-9c31-ed00230be90c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/FinitePlacement.lean:L34-L58
-- (upload_full_project.md Phase 4): solution for node OAI.CompactBanach.finite_placement. The node keeps its source
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
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateSupport
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateMap
import Theorems.Thm_OAI_CompactBanach_coordinateMap_single
import Theorems.Thm_OAI_CompactBanach_exists_auerbach_vectors
import Theorems.Thm_OAI_CompactBanach_finite_coordinate_support
import Theorems.Thm_OAI_CompactBanach_norm_map_point_sub_le
import Theorems.Thm_OAI_DoublingHilbert_point_dist_sq

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

/-- Distinct choices at one level are at least one scale apart. -/
theorem scale_le_norm_entryVector_sub {w w' : Tuple} {j : ℕ} (hne : w j ≠ w' j) :
    scale j ≤ ‖entryVector w j - entryVector w' j‖ := by
  by_cases hw : w j = 0
  · have hw' : w' j ≠ 0 := by intro h; exact hne (hw.trans h.symm)
    simp [hw, hw']
  · by_cases hw' : w' j = 0
    · simp [hw, hw']
    · rw [entryVector_of_ne_zero hw, entryVector_of_ne_zero hw']
      have hpred : w j - 1 ≠ w' j - 1 := by omega
      have hs := norm_levelVector_sub_sq j (w j - 1) (w' j - 1) hpred
      nlinarith [scale_pos j, norm_nonneg (levelVector j (w j - 1) - levelVector j (w' j - 1))]

/-- Every individual level distance is no larger than the whole source distance. -/
theorem norm_entryVector_sub_le_dist (p q : Base) (w w' : Tuple) (j : ℕ) :
    ‖entryVector w j - entryVector w' j‖ ≤ dist (point p w) (point q w') := by
  classical
  let s := insert j (w.support ∪ w'.support)
  have hw : w.support ⊆ s := fun m hm => Finset.mem_insert_of_mem (Finset.mem_union_left _ hm)
  have hw' : w'.support ⊆ s := fun m hm => Finset.mem_insert_of_mem (Finset.mem_union_right _ hm)
  have hdist := point_dist_sq p q w w' s hw hw'
  have hj := Finset.single_le_sum (f := fun m => ‖entryVector w m - entryVector w' m‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_insert_self j (w.support ∪ w'.support))
  nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2), dist_nonneg (x := point p w) (y := point q w')]

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

-- ---- from OAI.Geometry.DoublingHilbert.SparseCoordinates ----
namespace OAI

open Set Metric
noncomputable section
namespace CompactBanach
open DoublingHilbert

                                                                   
theorem norm_map_point_sub_le_dist {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (T : RealL2 →ₗ[ℝ] B) (hT : ∀ i a, ‖T (lp.single 2 i a)‖ ≤ |a|)
    (p q : Base) (w w' : Tuple) :
    ‖T (point p w - point q w')‖ ≤ 6 * dist (point p w) (point q w') :=
  norm_map_point_sub_le T hT p q w w' dist_nonneg
    (abs_fst_sub_le_dist p q w w') (abs_snd_sub_le_dist p q w w')
    (fun j hj => (scale_le_norm_entryVector_sub hj).trans (norm_entryVector_sub_le_dist p q w w' j))

end CompactBanach
end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.CoordinateSupport ----
namespace OAI

open Set Metric
noncomputable section
namespace CompactBanach
open DoublingHilbert

theorem point_apply_coordinate (p : Base) (w : Tuple) (j i : ℕ) :
    point p w (coordinate j i) =
      if w j ≠ 0 ∧ w j - 1 = i then scale j else 0 := by
  classical
  simp only [point, lp.coeFn_add, Pi.add_apply, baseVector, tupleVector, lp.coeFn_sum,
    Finset.sum_apply, levelVector]
  simp only [lp.single_apply_ne _ _ _ (coordinate_ne_zero j i),
    lp.single_apply_ne _ _ _ (coordinate_ne_one j i), zero_add]
  simp [lp.single_apply, Pi.single_apply, coordinate_eq_iff, ite_and, eq_comm]

                                                                        
theorem exists_coordinate_difference {p q : Base} {w w' : Tuple} {j : ℕ}
    (hj : w j ≠ w' j) :
    ∃ i, |point p w i - point q w' i| = scale j := by
  by_cases hw : w j = 0
  · have hw' : w' j ≠ 0 := by omega
    refine ⟨coordinate j (w' j - 1), ?_⟩
    simp [point_apply_coordinate, hw, hw', abs_of_pos (scale_pos j)]
  · refine ⟨coordinate j (w j - 1), ?_⟩
    have hn : ¬ (w' j ≠ 0 ∧ w' j - 1 = w j - 1) := by omega
    simp [point_apply_coordinate, hw, hn, abs_of_pos (scale_pos j)]

end CompactBanach
end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.CoordinateMap ----
namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach
open DoublingHilbert

theorem coordinateMap_lower {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (I : Finset ℕ) (v : I → B)
    (hv : ∀ (c : I → ℝ) i, |c i| ≤ ‖∑ j, c j • v j‖)
    (z : RealL2) (hz : ∀ i ∉ I, z i = 0) :
    ∀ i, |z i| ≤ ‖coordinateMap I v z‖ := by
  intro i
  by_cases hi : i ∈ I
  · exact hv (fun j => z j) ⟨i, hi⟩
  · rw [hz i hi, abs_zero]
    exact norm_nonneg _

end CompactBanach
end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.FinitePlacement ----
namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach
open DoublingHilbert

theorem dist_point_le_of_coordinate_bound (p q : Base) (w w' : Tuple) {R : ℝ}
    (hR : 0 ≤ R) (hc : ∀ i, |point p w i - point q w' i| ≤ R) :
    dist (point p w) (point q w') ≤ 6 * R := by
  have hf : |p.1 - q.1| ≤ R := by simpa using hc 0
  have hs : |p.2 - q.2| ≤ R := by simpa using hc 1
  have hw : ∀ j, w j ≠ w' j → scale j ≤ R := by
    intro j hj
    obtain ⟨i, hi⟩ := exists_coordinate_difference (p := p) (q := q) hj
    exact hi ▸ hc i
  have ht := norm_map_point_sub_le (LinearMap.id : RealL2 →ₗ[ℝ] RealL2)
    (fun i a => by simp only [LinearMap.id_apply,
      lp.norm_single (by norm_num : (0 : ENNReal) < 2), Real.norm_eq_abs]; rfl)
    p q w w' hR hf hs hw
  simpa only [LinearMap.id_apply, dist_eq_norm] using ht

                                                                                   
                                                                               
                                                                         
theorem finite_placement {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (hB : ¬ FiniteDimensional ℝ B) (X : Finset RealL2)
    (hX : ∀ z ∈ X, z ∈ constructedSet) :
    ∃ T : RealL2 →ₗ[ℝ] B, ∀ x ∈ X, ∀ y ∈ X,
       dist x y / 6 ≤ dist (T x) (T y) ∧ dist (T x) (T y) ≤ 6 * dist x y := by
  classical
  obtain ⟨I, hI⟩ := finite_coordinate_support X hX
  obtain ⟨v, hv, hvc⟩ := exists_auerbach_vectors (ι := I) hB
  let T := coordinateMap I v
  have hT : ∀ i a, ‖T (lp.single 2 i a)‖ ≤ |a| := coordinateMap_single I v hv
  refine ⟨T, ?_⟩
  intro x hx y hy
  have hcoords : ∀ i, |(x - y) i| ≤ ‖T (x - y)‖ :=
    coordinateMap_lower I v hvc (x - y) (by
      intro i hi
      change x i - y i = 0
      rw [hI x hx i hi, hI y hy i hi, sub_self])
  obtain ⟨p, w, _, rfl⟩ := hX x hx
  obtain ⟨q, w', _, rfl⟩ := hX y hy
  have hlow := dist_point_le_of_coordinate_bound p q w w' (norm_nonneg (T _)) hcoords
  have hupp := norm_map_point_sub_le_dist T hT p q w w'
  rw [map_sub, ← dist_eq_norm] at hlow hupp
  constructor
  · linarith
  · exact hupp

end CompactBanach
end

end OAI

-- ---- platform node ----
open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators
open DoublingHilbert


theorem solution : type_of% @_root_.OAI.CompactBanach.finite_placement := @_root_.OAI.CompactBanach.finite_placement
