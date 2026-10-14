-- Prove2me | solution 1 for KerrBL.ginv_mul_g_Kerr
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-09-09T09:37:38.047373+00:00
-- url     : https://prove2.me/submissions/d556ac15-9b64-4f93-bd24-773d8c27c5a6

import Definitions.Def_KerrBL_Kerr_Metric
import Mathlib.Tactic
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open KerrBL Filter Topology

namespace KerrBL

theorem termKerr_inv00_0 (M a : ℝ) (r s c S D : ℝ) (hS : S ≠ 0) (hD : D ≠ 0) (hs : s ≠ 0) :
    (D*a^(2:ℕ)*s^(2:ℕ) - (a^(2:ℕ) + r^(2:ℕ))^(2:ℕ))/((S*D)) * ((-1) + 2*M*r/S) = (((-2))*M*r^(5:ℕ) + S*a^(4:ℕ) + S*r^(4:ℕ) - 4*M*a^(2:ℕ)*r^(3:ℕ) - 2*M*r*a^(4:ℕ) + 2*S*a^(2:ℕ)*r^(2:ℕ) - S*D*a^(2:ℕ)*s^(2:ℕ) + 2*M*r*D*a^(2:ℕ)*s^(2:ℕ))/(D*S^(2:ℕ)) := by
  first | ring1 | (field_simp; ring1) | field_simp

theorem termKerr_inv00_1 (M a : ℝ) (r s c S D : ℝ) (hS : S ≠ 0) (hD : D ≠ 0) (hs : s ≠ 0) :
    ((-2))*M*a*r/((S*D)) * (((-2))*M*a*r*s^(2:ℕ)/S) = (4*M^(2:ℕ)*a^(2:ℕ)*r^(2:ℕ)*s^(2:ℕ))/(D*S^(2:ℕ)) := by
  first | ring1 | (field_simp; ring1) | field_simp

theorem polyKerr_inv00 (M a : ℝ) (r s c S D : ℝ) (hp : s^(2:ℕ) + c^(2:ℕ) = 1) (hS' : S = r^(2:ℕ) + a^(2:ℕ)*c^(2:ℕ)) (hD' : D = a^(2:ℕ) + r^(2:ℕ) - 2*M*r) :
    (((-2))*M*r^(5:ℕ) + S*a^(4:ℕ) + S*r^(4:ℕ) - 4*M*a^(2:ℕ)*r^(3:ℕ) - 2*M*r*a^(4:ℕ) + 2*S*a^(2:ℕ)*r^(2:ℕ) - S*D*a^(2:ℕ)*s^(2:ℕ) + 2*M*r*D*a^(2:ℕ)*s^(2:ℕ)) + (4*M^(2:ℕ)*a^(2:ℕ)*r^(2:ℕ)*s^(2:ℕ)) = D*S^(2:ℕ) := by
  linear_combination (-(a^(2:ℕ)*r^(4:ℕ)) - a^(4:ℕ)*r^(2:ℕ) - a^(6:ℕ)*c^(2:ℕ) + 4*M*a^(2:ℕ)*r^(3:ℕ) + 2*M*r*a^(4:ℕ) - a^(4:ℕ)*r^(2:ℕ)*c^(2:ℕ) + 2*M*r*a^(4:ℕ)*c^(2:ℕ)) * hp + (a^(4:ℕ) + r^(4:ℕ) - S*D - D*r^(2:ℕ) + 2*a^(2:ℕ)*r^(2:ℕ) - D*a^(2:ℕ)*c^(2:ℕ) - D*a^(2:ℕ)*s^(2:ℕ)) * hS' + (-(r^(4:ℕ)) - a^(4:ℕ)*c^(4:ℕ) - 2*a^(2:ℕ)*r^(2:ℕ)*c^(2:ℕ) - a^(2:ℕ)*r^(2:ℕ)*s^(2:ℕ) - a^(4:ℕ)*s^(2:ℕ)*c^(2:ℕ) + 2*M*r*a^(2:ℕ)*s^(2:ℕ)) * hD'

theorem ginvgKerr_00 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 0 k x * gKerr M a k 0 x) = 1 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]
  have key := polyKerr_inv00 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) (Real.sin_sq_add_cos_sq _) (by unfold Sig; ring) (by unfold Del; ring)
  rw [termKerr_inv00_0 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) hS hD hs, termKerr_inv00_1 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) hS hD hs]
  try simp only [← neg_div, ← add_div, ← sub_div]
  rw [div_eq_one_iff_eq (by positivity)]
  first | done | linear_combination key

theorem ginvgKerr_01 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 0 k x * gKerr M a k 1 x) = 0 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]

theorem ginvgKerr_02 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 0 k x * gKerr M a k 2 x) = 0 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]

theorem termKerr_inv03_0 (M a : ℝ) (r s c S D : ℝ) (hS : S ≠ 0) (hD : D ≠ 0) (hs : s ≠ 0) :
    (D*a^(2:ℕ)*s^(2:ℕ) - (a^(2:ℕ) + r^(2:ℕ))^(2:ℕ))/((S*D)) * (((-2))*M*a*r*s^(2:ℕ)/S) = (2*M*a*r^(5:ℕ)*s^(2:ℕ) + 4*M*a^(3:ℕ)*r^(3:ℕ)*s^(2:ℕ) + 2*M*r*a^(5:ℕ)*s^(2:ℕ) - 2*M*r*D*a^(3:ℕ)*s^(4:ℕ))/(D*S^(2:ℕ)) := by
  first | ring1 | (field_simp; ring1) | field_simp

theorem termKerr_inv03_1 (M a : ℝ) (r s c S D : ℝ) (hS : S ≠ 0) (hD : D ≠ 0) (hs : s ≠ 0) :
    ((-2))*M*a*r/((S*D)) * (s^(2:ℕ)*(a^(2:ℕ) + r^(2:ℕ) + 2*M*r*a^(2:ℕ)*s^(2:ℕ)/S)) = (((-4))*M^(2:ℕ)*a^(3:ℕ)*r^(2:ℕ)*s^(4:ℕ) - 2*M*a*S*r^(3:ℕ)*s^(2:ℕ) - 2*M*r*S*a^(3:ℕ)*s^(2:ℕ))/(D*S^(2:ℕ)) := by
  first | ring1 | (field_simp; ring1) | field_simp

theorem polyKerr_inv03 (M a : ℝ) (r s c S D : ℝ) (hp : s^(2:ℕ) + c^(2:ℕ) = 1) (hS' : S = r^(2:ℕ) + a^(2:ℕ)*c^(2:ℕ)) (hD' : D = a^(2:ℕ) + r^(2:ℕ) - 2*M*r) :
    (2*M*a*r^(5:ℕ)*s^(2:ℕ) + 4*M*a^(3:ℕ)*r^(3:ℕ)*s^(2:ℕ) + 2*M*r*a^(5:ℕ)*s^(2:ℕ) - 2*M*r*D*a^(3:ℕ)*s^(4:ℕ)) + (((-4))*M^(2:ℕ)*a^(3:ℕ)*r^(2:ℕ)*s^(4:ℕ) - 2*M*a*S*r^(3:ℕ)*s^(2:ℕ) - 2*M*r*S*a^(3:ℕ)*s^(2:ℕ)) = 0 := by
  linear_combination (((-2))*M*a^(3:ℕ)*r^(3:ℕ)*s^(2:ℕ) - 2*M*r*a^(5:ℕ)*s^(2:ℕ)) * hp + (((-2))*M*a*r^(3:ℕ)*s^(2:ℕ) - 2*M*r*a^(3:ℕ)*s^(2:ℕ)) * hS' + (((-2))*M*r*a^(3:ℕ)*s^(4:ℕ)) * hD'

theorem ginvgKerr_03 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 0 k x * gKerr M a k 3 x) = 0 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]
  have key := polyKerr_inv03 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) (Real.sin_sq_add_cos_sq _) (by unfold Sig; ring) (by unfold Del; ring)
  rw [termKerr_inv03_0 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) hS hD hs, termKerr_inv03_1 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) hS hD hs]
  try simp only [← neg_div, ← add_div, ← sub_div]
  rw [div_eq_zero_iff]
  left
  first | done | linear_combination key

theorem ginvgKerr_10 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 1 k x * gKerr M a k 0 x) = 0 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]

theorem termKerr_inv11_0 (M a : ℝ) (r s c S D : ℝ) (hS : S ≠ 0) (hD : D ≠ 0) (hs : s ≠ 0) :
    D/S * (S/D) = (S*D)/(S*D) := by
  first | ring1 | (field_simp; ring1) | field_simp

theorem polyKerr_inv11 (M a : ℝ) (r s c S D : ℝ) (hp : s^(2:ℕ) + c^(2:ℕ) = 1) (hS' : S = r^(2:ℕ) + a^(2:ℕ)*c^(2:ℕ)) (hD' : D = a^(2:ℕ) + r^(2:ℕ) - 2*M*r) :
    (S*D) = S*D := by
  linear_combination (0) * hp + (0) * hS' + (0) * hD'

theorem ginvgKerr_11 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 1 k x * gKerr M a k 1 x) = 1 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]
  have key := polyKerr_inv11 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) (Real.sin_sq_add_cos_sq _) (by unfold Sig; ring) (by unfold Del; ring)
  rw [termKerr_inv11_0 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) hS hD hs]
  try simp only [← neg_div, ← add_div, ← sub_div]
  rw [div_eq_one_iff_eq (by positivity)]
  first | done | linear_combination key

theorem ginvgKerr_12 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 1 k x * gKerr M a k 2 x) = 0 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]

theorem ginvgKerr_13 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 1 k x * gKerr M a k 3 x) = 0 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]

theorem ginvgKerr_20 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 2 k x * gKerr M a k 0 x) = 0 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]

theorem ginvgKerr_21 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 2 k x * gKerr M a k 1 x) = 0 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]

theorem termKerr_inv22_0 (M a : ℝ) (r s c S D : ℝ) (hS : S ≠ 0) (hD : D ≠ 0) (hs : s ≠ 0) :
    1/S * (S) = (S)/(S) := by
  first | ring1 | (field_simp; ring1) | field_simp

theorem polyKerr_inv22 (M a : ℝ) (r s c S D : ℝ) (hp : s^(2:ℕ) + c^(2:ℕ) = 1) (hS' : S = r^(2:ℕ) + a^(2:ℕ)*c^(2:ℕ)) (hD' : D = a^(2:ℕ) + r^(2:ℕ) - 2*M*r) :
    (S) = S := by
  linear_combination (0) * hp + (0) * hS' + (0) * hD'

theorem ginvgKerr_22 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 2 k x * gKerr M a k 2 x) = 1 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]
  have key := polyKerr_inv22 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) (Real.sin_sq_add_cos_sq _) (by unfold Sig; ring) (by unfold Del; ring)
  rw [termKerr_inv22_0 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) hS hD hs]
  try simp only [← neg_div, ← add_div, ← sub_div]
  rw [div_eq_one_iff_eq (by positivity)]
  first | done | linear_combination key

theorem ginvgKerr_23 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 2 k x * gKerr M a k 3 x) = 0 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]

theorem termKerr_inv30_0 (M a : ℝ) (r s c S D : ℝ) (hS : S ≠ 0) (hD : D ≠ 0) (hs : s ≠ 0) :
    ((-2))*M*a*r/((S*D)) * ((-1) + 2*M*r/S) = (((-4))*a*M^(2:ℕ)*r^(2:ℕ)*s^(2:ℕ) + 2*M*a*r*S*s^(2:ℕ))/(D*s^(2:ℕ)*S^(2:ℕ)) := by
  first | ring1 | (field_simp; ring1) | field_simp

theorem termKerr_inv30_1 (M a : ℝ) (r s c S D : ℝ) (hS : S ≠ 0) (hD : D ≠ 0) (hs : s ≠ 0) :
    (D - a^(2:ℕ)*s^(2:ℕ))/((S*D*s^(2:ℕ))) * (((-2))*M*a*r*s^(2:ℕ)/S) = (2*M*r*a^(3:ℕ)*s^(4:ℕ) - 2*M*a*r*D*s^(2:ℕ))/(D*s^(2:ℕ)*S^(2:ℕ)) := by
  first | ring1 | (field_simp; ring1) | field_simp

theorem polyKerr_inv30 (M a : ℝ) (r s c S D : ℝ) (hp : s^(2:ℕ) + c^(2:ℕ) = 1) (hS' : S = r^(2:ℕ) + a^(2:ℕ)*c^(2:ℕ)) (hD' : D = a^(2:ℕ) + r^(2:ℕ) - 2*M*r) :
    (((-4))*a*M^(2:ℕ)*r^(2:ℕ)*s^(2:ℕ) + 2*M*a*r*S*s^(2:ℕ)) + (2*M*r*a^(3:ℕ)*s^(4:ℕ) - 2*M*a*r*D*s^(2:ℕ)) = 0 := by
  linear_combination (2*M*r*a^(3:ℕ)*s^(2:ℕ)) * hp + (2*M*a*r*s^(2:ℕ)) * hS' + (((-2))*M*a*r*s^(2:ℕ)) * hD'

theorem ginvgKerr_30 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 3 k x * gKerr M a k 0 x) = 0 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]
  have key := polyKerr_inv30 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) (Real.sin_sq_add_cos_sq _) (by unfold Sig; ring) (by unfold Del; ring)
  rw [termKerr_inv30_0 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) hS hD hs, termKerr_inv30_1 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) hS hD hs]
  try simp only [← neg_div, ← add_div, ← sub_div]
  rw [div_eq_zero_iff]
  left
  first | done | linear_combination key

theorem ginvgKerr_31 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 3 k x * gKerr M a k 1 x) = 0 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]

theorem ginvgKerr_32 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 3 k x * gKerr M a k 2 x) = 0 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]

theorem termKerr_inv33_0 (M a : ℝ) (r s c S D : ℝ) (hS : S ≠ 0) (hD : D ≠ 0) (hs : s ≠ 0) :
    ((-2))*M*a*r/((S*D)) * (((-2))*M*a*r*s^(2:ℕ)/S) = (4*M^(2:ℕ)*a^(2:ℕ)*r^(2:ℕ)*s^(4:ℕ))/(D*s^(2:ℕ)*S^(2:ℕ)) := by
  first | ring1 | (field_simp; ring1) | field_simp

theorem termKerr_inv33_1 (M a : ℝ) (r s c S D : ℝ) (hS : S ≠ 0) (hD : D ≠ 0) (hs : s ≠ 0) :
    (D - a^(2:ℕ)*s^(2:ℕ))/((S*D*s^(2:ℕ))) * (s^(2:ℕ)*(a^(2:ℕ) + r^(2:ℕ) + 2*M*r*a^(2:ℕ)*s^(2:ℕ)/S)) = (-(S*a^(4:ℕ)*s^(4:ℕ)) + S*D*a^(2:ℕ)*s^(2:ℕ) + S*D*r^(2:ℕ)*s^(2:ℕ) - 2*M*r*a^(4:ℕ)*s^(6:ℕ) - S*a^(2:ℕ)*r^(2:ℕ)*s^(4:ℕ) + 2*M*r*D*a^(2:ℕ)*s^(4:ℕ))/(D*s^(2:ℕ)*S^(2:ℕ)) := by
  first | ring1 | (field_simp; ring1) | field_simp

theorem polyKerr_inv33 (M a : ℝ) (r s c S D : ℝ) (hp : s^(2:ℕ) + c^(2:ℕ) = 1) (hS' : S = r^(2:ℕ) + a^(2:ℕ)*c^(2:ℕ)) (hD' : D = a^(2:ℕ) + r^(2:ℕ) - 2*M*r) :
    (4*M^(2:ℕ)*a^(2:ℕ)*r^(2:ℕ)*s^(4:ℕ)) + (-(S*a^(4:ℕ)*s^(4:ℕ)) + S*D*a^(2:ℕ)*s^(2:ℕ) + S*D*r^(2:ℕ)*s^(2:ℕ) - 2*M*r*a^(4:ℕ)*s^(6:ℕ) - S*a^(2:ℕ)*r^(2:ℕ)*s^(4:ℕ) + 2*M*r*D*a^(2:ℕ)*s^(4:ℕ)) = D*s^(2:ℕ)*S^(2:ℕ) := by
  linear_combination (-(a^(2:ℕ)*r^(4:ℕ)*s^(2:ℕ)) - a^(4:ℕ)*r^(2:ℕ)*s^(2:ℕ) - a^(6:ℕ)*s^(2:ℕ)*c^(2:ℕ) + 2*M*a^(2:ℕ)*r^(3:ℕ)*s^(2:ℕ) - 2*M*r*a^(4:ℕ)*s^(4:ℕ) - a^(4:ℕ)*r^(2:ℕ)*s^(2:ℕ)*c^(2:ℕ) + 2*M*r*a^(4:ℕ)*s^(2:ℕ)*c^(2:ℕ)) * hp + (-(a^(4:ℕ)*s^(4:ℕ)) - S*D*s^(2:ℕ) + D*a^(2:ℕ)*s^(2:ℕ) - a^(2:ℕ)*r^(2:ℕ)*s^(4:ℕ) - D*a^(2:ℕ)*s^(2:ℕ)*c^(2:ℕ)) * hS' + (a^(2:ℕ)*r^(2:ℕ)*s^(2:ℕ) + a^(4:ℕ)*s^(2:ℕ)*c^(2:ℕ) - a^(4:ℕ)*s^(2:ℕ)*c^(4:ℕ) + 2*M*r*a^(2:ℕ)*s^(4:ℕ) - a^(2:ℕ)*r^(2:ℕ)*s^(2:ℕ)*c^(2:ℕ)) * hD'

theorem ginvgKerr_33 (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    (∑ k : Fin 4, giKerr M a 3 k x * gKerr M a k 3 x) = 1 := by
  obtain ⟨hS, hD, hs⟩ := hx
  simp only [Fin.sum_univ_four, gKerr_00, gKerr_01, gKerr_02, gKerr_03, gKerr_10, gKerr_11, gKerr_12, gKerr_13, gKerr_20, gKerr_21, gKerr_22, gKerr_23, gKerr_30, gKerr_31, gKerr_32, gKerr_33, giKerr_00, giKerr_01, giKerr_02, giKerr_03, giKerr_10, giKerr_11, giKerr_12, giKerr_13, giKerr_20, giKerr_21, giKerr_22, giKerr_23, giKerr_30, giKerr_31, giKerr_32, giKerr_33, mul_zero, zero_mul, add_zero, zero_add]
  have key := polyKerr_inv33 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) (Real.sin_sq_add_cos_sq _) (by unfold Sig; ring) (by unfold Del; ring)
  rw [termKerr_inv33_0 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) hS hD hs, termKerr_inv33_1 M a (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) hS hD hs]
  try simp only [← neg_div, ← add_div, ← sub_div]
  rw [div_eq_one_iff_eq (by positivity)]
  first | done | linear_combination key

end KerrBL

/- Layer I: the closed-form inverse really inverts the metric on the regular domain. -/
theorem solution (M a : ℝ) (x : Pt) (hx : RegKerr M a x) (i j : Fin 4) :
    (∑ k : Fin 4, giKerr M a i k x * gKerr M a k j x) = (if i = j then 1 else 0) := by
  fin_cases i <;> fin_cases j
  · rw [if_pos rfl]; exact ginvgKerr_00 M a x hx
  · rw [if_neg (by decide)]; exact ginvgKerr_01 M a x hx
  · rw [if_neg (by decide)]; exact ginvgKerr_02 M a x hx
  · rw [if_neg (by decide)]; exact ginvgKerr_03 M a x hx
  · rw [if_neg (by decide)]; exact ginvgKerr_10 M a x hx
  · rw [if_pos rfl]; exact ginvgKerr_11 M a x hx
  · rw [if_neg (by decide)]; exact ginvgKerr_12 M a x hx
  · rw [if_neg (by decide)]; exact ginvgKerr_13 M a x hx
  · rw [if_neg (by decide)]; exact ginvgKerr_20 M a x hx
  · rw [if_neg (by decide)]; exact ginvgKerr_21 M a x hx
  · rw [if_pos rfl]; exact ginvgKerr_22 M a x hx
  · rw [if_neg (by decide)]; exact ginvgKerr_23 M a x hx
  · rw [if_neg (by decide)]; exact ginvgKerr_30 M a x hx
  · rw [if_neg (by decide)]; exact ginvgKerr_31 M a x hx
  · rw [if_neg (by decide)]; exact ginvgKerr_32 M a x hx
  · rw [if_pos rfl]; exact ginvgKerr_33 M a x hx
