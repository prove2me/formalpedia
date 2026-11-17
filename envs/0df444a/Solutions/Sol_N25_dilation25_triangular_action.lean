-- Prove2me | solution 1 for N25.dilation25_triangular_action
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:32.3013+00:00
-- url     : https://prove2.me/submissions/885f90cd-c6c0-4de6-9198-fb30d9015529

import Mathlib

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

namespace N25

private theorem fraction_affine (a b c f r e : ℂ) (he : e ≠ 0) :
    (a * (r / e) + b) / (c * (r / e) + f) =
      (a * r + b * e) / (c * r + f * e) := by
  have h (x y : ℂ) : x * (r / e) + y = (x * r + y * e) / e := by
    field_simp
  rw [h, h, div_div_div_cancel_right₀ he]

/-- The integral triangularization gives the actual upper-half-plane argument. -/
theorem _root_.solution
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (d e v : ℤ)
    (hd : 0 < d) (he : 0 < e)
    (h : !![(25 : ℤ), 0; 0, 1] * (A : Matrix (Fin 2) (Fin 2) ℤ) =
      (B : Matrix (Fin 2) (Fin 2) ℤ) * !![d, v; 0, e]) (τ : UpperHalfPlane) :
    ∃ z : UpperHalfPlane, (z : ℂ) = ((d : ℂ) * (τ : ℂ) + (v : ℂ)) / (e : ℂ) ∧
      ((B • z : UpperHalfPlane) : ℂ) = 25 * ((A • τ : UpperHalfPlane) : ℂ) := by
  let z : UpperHalfPlane :=
    ⟨(((d : ℝ) / (e : ℝ) : ℝ) : ℂ) * (τ : ℂ) + (((v : ℝ) / (e : ℝ) : ℝ) : ℂ), by
      simpa using mul_pos (div_pos (by exact_mod_cast hd : (0 : ℝ) < d)
        (by exact_mod_cast he : (0 : ℝ) < e)) τ.im_pos⟩
  have heC : (e : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt he
  have hz : (z : ℂ) = ((d : ℂ) * (τ : ℂ) + (v : ℂ)) / (e : ℂ) := by
    dsimp [z]
    push_cast
    ring
  have h00 : (25 : ℤ) * A 0 0 = B 0 0 * d := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun m => m 0 0) h
  have h01 : (25 : ℤ) * A 0 1 = B 0 0 * v + B 0 1 * e := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun m => m 0 1) h
  have h10 : A 1 0 = B 1 0 * d := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun m => m 1 0) h
  have h11 : A 1 1 = B 1 0 * v + B 1 1 * e := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrArg (fun m => m 1 1) h
  have hc00 : (25 : ℂ) * (A 0 0 : ℂ) = (B 0 0 : ℂ) * (d : ℂ) := by exact_mod_cast h00
  have hc01 : (25 : ℂ) * (A 0 1 : ℂ) = (B 0 0 : ℂ) * (v : ℂ) + (B 0 1 : ℂ) * (e : ℂ) := by exact_mod_cast h01
  have hc10 : (A 1 0 : ℂ) = (B 1 0 : ℂ) * (d : ℂ) := by exact_mod_cast h10
  have hc11 : (A 1 1 : ℂ) = (B 1 0 : ℂ) * (v : ℂ) + (B 1 1 : ℂ) * (e : ℂ) := by exact_mod_cast h11
  refine ⟨z, hz, ?_⟩
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply, hz,
    fraction_affine _ _ _ _ _ _ heC]
  have hn : (B 0 0 : ℂ) * ((d : ℂ) * (τ : ℂ) + (v : ℂ)) + (B 0 1 : ℂ) * (e : ℂ) =
      25 * ((A 0 0 : ℂ) * (τ : ℂ) + (A 0 1 : ℂ)) := by
    linear_combination -(τ : ℂ) * hc00 - hc01
  have hden : (B 1 0 : ℂ) * ((d : ℂ) * (τ : ℂ) + (v : ℂ)) + (B 1 1 : ℂ) * (e : ℂ) =
      (A 1 0 : ℂ) * (τ : ℂ) + (A 1 1 : ℂ) := by
    linear_combination -(τ : ℂ) * hc10 - hc11
  have hcast (x : ℤ) : ((algebraMap ℤ ℝ x : ℝ) : ℂ) = (x : ℂ) := by
    change ((x : ℝ) : ℂ) = (x : ℂ)
    norm_cast
  simp only [hcast, hn, hden, mul_div_assoc]

end N25
