-- Prove2me | solution 1 for OAI.Problem160.properColoring_seven_of_normalized_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T17:45:29.185985+00:00
-- url     : https://prove2.me/submissions/968f351f-6cd1-49d7-9838-c0d5b17e3fc7

-- Generated from openai/math@1581d4c lean/OAI/Geometry/PlaneColoring/Seven.lean:L14-L32
-- (upload_full_project.md Phase 4): solution for node OAI.Problem160.properColoring_seven_of_normalized_cover. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_PlaneColoring
import Definitions.Def_OAI_Geometry_PlaneColoring_Lattice
import Definitions.Def_OAI_Geometry_PlaneColoring_Basic
import Definitions.Def_OAI_Geometry_PlaneColoring_Metric
import Definitions.Def_OAI_Geometry_PlaneColoring_MeasurableProper
import Theorems.Thm_OAI_Problem160_exists_unit_distance_coloring_of_center_cover

-- ---- inline helpers from OAI.Geometry.PlaneColoring.Lattice ----
namespace OAI

/-! Integer arithmetic for the classical seven-color triangular lattice. -/

namespace Problem160
namespace SevenLattice

lemma normSq_pos {a b : ℤ} (h : a ≠ 0 ∨ b ≠ 0) : 0 < normSq a b := by
  unfold normSq
  rcases h with ha | hb
  · have ha' : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith [sq_nonneg (a + 2 * b)]
  · have hb' : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    nlinarith [sq_nonneg (2 * a + b)]

lemma seven_dvd_normSq {a b : ℤ} (h : 7 ∣ a + 3 * b) : 7 ∣ normSq a b := by
  have hi : normSq a b = (a + 3 * b) * (a - 2 * b) + 7 * b ^ 2 := by
    unfold normSq
    ring
  rw [hi]
  exact dvd_add (dvd_mul_of_dvd_left h _) (dvd_mul_right _ _)

lemma normSq_ge_seven {a b : ℤ} (h : 7 ∣ a + 3 * b)
    (hn : a ≠ 0 ∨ b ≠ 0) : 7 ≤ normSq a b := by
  exact Int.le_of_dvd (normSq_pos hn) (seven_dvd_normSq h)

lemma color_eq_iff_dvd {a b c d : ℤ} :
    color a b = color c d ↔ 7 ∣ (a - c) + 3 * (b - d) := by
  have hd := ZMod.intCast_zmod_eq_zero_iff_dvd ((a - c) + 3 * (b - d)) 7
  norm_num only [Nat.cast_ofNat] at hd
  rw [← hd]
  change color a b = color c d ↔ (((a - c) + 3 * (b - d) : ℤ) : ZMod 7) = 0
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  unfold color
  constructor <;> intro h <;> linear_combination h

lemma same_color_separation {a b c d : ℤ} (hc : color a b = color c d)
    (hne : (a, b) ≠ (c, d)) : 7 ≤ normSq (a - c) (b - d) := by
  apply normSq_ge_seven (color_eq_iff_dvd.mp hc)
  by_contra h
  push Not at h
  apply hne
  apply Prod.ext <;> omega

lemma colorFin_injective_value {a b c d : ℤ}
    (h : colorFin a b = colorFin c d) : color a b = color c d := h

end SevenLattice
end Problem160

end OAI

-- ---- inline helpers from OAI.Geometry.PlaneColoring.Metric ----
namespace OAI

noncomputable section

namespace Problem160

theorem triangularLattice_norm_sq (a b : ℤ) :
    ‖triangularLattice a b‖ ^ 2 =
      (16 / 25 : ℝ) * ((a : ℝ)^2 + (a : ℝ)*b + (b : ℝ)^2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, triangularLattice_zero, triangularLattice_one]
  ring_nf
  norm_num
  ring

theorem triangularLattice_sub (a b c d : ℤ) :
    triangularLattice a b - triangularLattice c d = triangularLattice (a-c) (b-d) := by
  ext i
  fin_cases i <;> simp [triangularLattice] <;> ring

theorem triangularLattice_dist_sq (a b c d : ℤ) :
    dist (triangularLattice a b) (triangularLattice c d) ^ 2 =
      (16 / 25 : ℝ) * (((a-c : ℤ) : ℝ)^2 +
        ((a-c : ℤ) : ℝ)*(b-d : ℤ) + ((b-d : ℤ) : ℝ)^2) := by
  rw [dist_eq_norm, triangularLattice_sub, triangularLattice_norm_sq]

theorem triangularLattice_dist_gt_two (a b c d : ℤ)
    (h : 7 ≤ (a-c)^2 + (a-c)*(b-d) + (b-d)^2) :
    (2 : ℝ) < dist (triangularLattice a b) (triangularLattice c d) := by
  have hr : (7 : ℝ) ≤ ((a-c : ℤ) : ℝ)^2 +
      ((a-c : ℤ) : ℝ)*(b-d : ℤ) + ((b-d : ℤ) : ℝ)^2 := by
    exact_mod_cast h
  have heq := triangularLattice_dist_sq a b c d
  have hd := dist_nonneg (x := triangularLattice a b) (y := triangularLattice c d)
  nlinarith

theorem dist_triangularLattice_sq (x : Plane) (a b : ℤ) :
    dist x (triangularLattice a b)^2 =
      (16 / 25 : ℝ) *
        (((5 / 4 : ℝ) * x 0 - ((a : ℝ) + (b : ℝ)/2))^2 +
         ((5 / 4 : ℝ) * x 1 - Real.sqrt 3 * b / 2)^2) := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, triangularLattice_zero,
    triangularLattice_one]
  ring

theorem dist_triangularLattice_le_of_coordinates (x : Plane) (a b : ℤ)
    (h : ((5 / 4 : ℝ) * x 0 - ((a : ℝ) + (b : ℝ)/2))^2 +
         ((5 / 4 : ℝ) * x 1 - Real.sqrt 3 * b / 2)^2 ≤ (1 / 3 : ℝ)) :
    dist x (triangularLattice a b) ≤ (7 / 15 : ℝ) := by
  have heq := dist_triangularLattice_sq x a b
  have hd := dist_nonneg (x := x) (y := triangularLattice a b)
  nlinarith

end Problem160

end

end OAI

-- ---- hoisted node ----
open OAI OAI.Problem160

theorem solution
    (hcover : ∀ x y : ℝ, ∃ a b : ℤ,
      (x - ((a : ℝ) + (b : ℝ) / 2)) ^ 2 +
        (y - Real.sqrt 3 * b / 2) ^ 2 ≤ (1 / 3 : ℝ)) :
    ProperColoring 7 := by
  apply exists_unit_distance_coloring_of_center_cover
    (fun p : ℤ × ℤ => triangularLattice p.1 p.2)
    (fun p : ℤ × ℤ => SevenLattice.colorFin p.1 p.2) (7 / 15 : ℝ)
  · intro x
    obtain ⟨a, b, hab⟩ := hcover ((5 / 4 : ℝ) * x 0) ((5 / 4 : ℝ) * x 1)
    exact ⟨(a, b), dist_triangularLattice_le_of_coordinates x a b hab⟩
  · norm_num
  · intro i j hij hc
    have hq := SevenLattice.same_color_separation
      (SevenLattice.colorFin_injective_value hc) hij
    have hsep := triangularLattice_dist_gt_two i.1 i.2 j.1 j.2 hq
    linarith
