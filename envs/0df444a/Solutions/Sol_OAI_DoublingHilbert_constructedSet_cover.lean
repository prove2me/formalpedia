-- Prove2me | solution 1 for OAI.DoublingHilbert.constructedSet_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:52:04.431998+00:00
-- url     : https://prove2.me/submissions/0b519ece-47b2-4826-a837-851a1d9a84a6

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Doubling.lean:L257-L280
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.constructedSet_cover. The node keeps its source
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
import Theorems.Thm_OAI_DoublingHilbert_source_cover_of_label

-- ---- from OAI.Geometry.DoublingHilbert.Construction ----
namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

theorem scale_succ (j : ℕ) : scale (j + 1) = scale j / 1000 := by
  simp [scale, pow_succ, div_eq_mul_inv]

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

theorem coarse_coordinate_eq {p q : Base} {w w' : Tuple} {t : ℝ}
    (hd : dist (point p w) (point q w') < t) {j : ℕ} (hj : t ≤ scale j) : w j = w' j := by
  by_contra hne
  exact (not_le_of_gt hd) (hj.trans ((scale_le_norm_entryVector_sub hne).trans
    (norm_entryVector_sub_le_dist p q w w' j)))

theorem scale_antitone : Antitone scale := by
  intro i j hij
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right hij 1)

theorem scale_le_div_of_lt {i j : ℕ} (hij : i < j) : scale j ≤ scale i / 1000 := by
  rw [← scale_succ]
  exact scale_antitone hij

theorem intermediate_unique {t : ℝ} {i j : ℕ}
    (hi : t / 64 < scale i ∧ scale i ≤ t) (hj : t / 64 < scale j ∧ scale j ≤ t) : i = j := by
  rcases lt_trichotomy i j with hij | heq | hji
  · have h := scale_le_div_of_lt hij
    have hp := scale_pos i
    linarith
  · exact heq
  · have h := scale_le_div_of_lt hji
    have hp := scale_pos j
    linarith

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

theorem nearbyStripIndices_card (c width : ℝ) : (nearbyStripIndices c width).card = 131 := by
  simp only [nearbyStripIndices, Int.card_Icc]
  omega

theorem mem_nearbyStripIndices {c width t x : ℝ} {q : ℤ}
    (hw : 0 < width) (ht : t / 64 < width) (hx : |x - c| < t)
    (hq : (q : ℝ) * width < x ∧ x < ((q : ℝ) + 1) * width) :
    q ∈ nearbyStripIndices c width := by
  have hxc := abs_lt.mp hx
  have hc₀ := Int.floor_le (c / width)
  have hc₁ := Int.lt_floor_add_one (c / width)
  have hc₀' := (le_div_iff₀ hw).mp hc₀
  have hc₁' := (div_lt_iff₀ hw).mp hc₁
  apply Finset.mem_Icc.mpr
  constructor <;> apply (Int.cast_le (R := ℝ)).mp
  · push_cast
    nlinarith
  · push_cast
    nlinarith

end DoublingHilbert

open Set Metric
noncomputable section
namespace DoublingHilbert

end DoublingHilbert

namespace DoublingHilbert
open Set
open scoped BigOperators

theorem nearbyLabels_card (c : Base) (j : ℕ) : (nearbyLabels c j).card ≤ 300 := by
  have h₁ := Finset.card_image_le (s := nearbyStripIndices c.2 (scale j))
    (f := fun q => (q % (colors j : ℤ)).toNat + 1)
  have h₂ := Finset.card_image_le (s := nearbyStripIndices c.1 ((widthFactor j : ℝ) * scale j))
    (f := fun q => (q % (colors j : ℤ)).toNat + 1)
  rw [nearbyStripIndices_card] at h₁ h₂
  unfold nearbyLabels
  exact (Finset.card_insert_le _ _).trans ((Nat.add_le_add_right
    (Finset.card_union_le _ _) 1).trans (by omega))

theorem admissible_mem_nearbyLabels {c p : Base} {w : Tuple} {j : ℕ} {t : ℝ}
    (hj : t / 64 < scale j) (hp₁ : |p.1 - c.1| < t) (hp₂ : |p.2 - c.2| < t)
    (hw : admissible p w) : w j ∈ nearbyLabels c j := by
  by_cases hzero : w j = 0
  · simp [hzero, nearbyLabels]
  · have ha := (hw j (Finsupp.mem_support_iff.mpr hzero)).2
    have hwid : 1 ≤ (widthFactor j : ℝ) := by exact_mod_cast widthFactor_pos j
    have hwpos : 0 < (widthFactor j : ℝ) * scale j :=
      mul_pos (by linarith) (scale_pos j)
    have hwle : scale j ≤ (widthFactor j : ℝ) * scale j := by nlinarith [scale_pos j]
    have heq {q : ℤ} (hq : q % (colors j : ℤ) = (w j - 1 : ℕ)) :
        (q % (colors j : ℤ)).toNat + 1 = w j := by
      rw [hq, Int.toNat_natCast]
      omega
    rcases ha with ⟨q, hq, hlo, hhi⟩ | ⟨q, hq, hlo, hhi⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨q, mem_nearbyStripIndices (scale_pos j) hj hp₂ ⟨hlo, hhi⟩, heq hq⟩))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨q, mem_nearbyStripIndices hwpos (hj.trans_le hwle) hp₁ ⟨hlo, hhi⟩, heq hq⟩))

theorem source_admissible (z : constructedSet) : admissible (sourceBase z) (sourceTuple z) :=
  (Classical.choose_spec (Classical.choose_spec z.prop)).1

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

theorem sourceTuple_coarse_eq {z z' : constructedSet} {t : ℝ} (hd : dist z z' < t)
    {j : ℕ} (hj : t ≤ scale j) : sourceTuple z j = sourceTuple z' j := by
  apply coarse_coordinate_eq (p := sourceBase z) (q := sourceBase z') (t := t) _ hj
  simpa only [← source_eq_point, Subtype.dist_eq] using hd

/-- The fixed Hilbert subset has an intrinsic open-ball doubling bound of 76800. -/
theorem constructedSet_cover (x : constructedSet) {t : ℝ} (ht : 0 < t) :
    ∃ centers : Finset constructedSet, centers.card ≤ 76800 ∧
      ∀ y : constructedSet, dist y x < t → ∃ c ∈ centers, dist y c < t / 2 := by
  classical
  by_cases hmid : ∃ j, t / 64 < scale j ∧ scale j ≤ t
  · obtain ⟨m, hm⟩ := hmid
    apply source_cover_of_label x ht (nearbyLabels (sourceBase x) m) (nearbyLabels_card _ _)
      (fun y => ⟨sourceTuple y.val m, admissible_mem_nearbyLabels hm.1
        ((sourceBase_fst_dist_le y.val x).trans_lt y.prop)
        ((sourceBase_snd_dist_le y.val x).trans_lt y.prop) (source_admissible y.val)⟩)
    intro y z hyz j hj
    by_cases hjt : scale j ≤ t
    · have heq := intermediate_unique ⟨hj, hjt⟩ hm
      subst j
      exact congrArg Subtype.val hyz
    · exact (sourceTuple_coarse_eq y.prop (le_of_not_ge hjt)).trans
        (sourceTuple_coarse_eq z.prop (le_of_not_ge hjt)).symm
  · apply source_cover_of_label x ht {0} (by simp) (fun _ => ⟨0, by simp⟩)
    intro y z _ j hj
    have hjt : t ≤ scale j := by
      by_contra hn
      exact hmid ⟨j, hj, (not_le.mp hn).le⟩
    exact (sourceTuple_coarse_eq y.prop hjt).trans (sourceTuple_coarse_eq z.prop hjt).symm

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

theorem solution (x : constructedSet) {t : ℝ} (ht : 0 < t) :
    ∃ centers : Finset constructedSet, centers.card ≤ 76800 ∧
      ∀ y : constructedSet, dist y x < t → ∃ c ∈ centers, dist y c < t / 2 := by
  first
    | exact OAI.DoublingHilbert.constructedSet_cover x ht
    | exact OAI.DoublingHilbert.constructedSet_cover
    | (apply OAI.DoublingHilbert.constructedSet_cover <;> assumption)
    | (intros; apply OAI.DoublingHilbert.constructedSet_cover <;> assumption)
