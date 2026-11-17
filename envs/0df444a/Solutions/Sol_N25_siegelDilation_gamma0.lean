-- Prove2me | solution 1 for N25.siegelDilation_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:23.016228+00:00
-- url     : https://prove2.me/submissions/fda022ae-dd02-46e0-b16e-600b6fee527f

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_siegelFun_specialLinearGroup_smul
import Theorems.Thm_N25_siegelFun_second_index_shift

set_option autoImplicit false

namespace N25

private theorem dilated_fraction (a b c d z : ℂ) :
    (a * (25 * z) + 25 * b) / (c * (25 * z) + d) =
      25 * ((a * z + b) / (25 * c * z + d)) := by
  rw [show c * (25 * z) + d = 25 * c * z + d by ring]
  ring

/-- Dilation conjugates a level-twenty-five matrix to an integral unimodular
matrix. Its common Siegel multiplier and the exact index shift give the
unpowered transformation simultaneously for all integer first indices. -/
theorem _root_.solution
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : (25 : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ∃ μ : ℂ, μ^12 = 1 ∧ ∀ (g : ℤ) (τ : UpperHalfPlane),
      -ModularCurve.siegelFun 25 g 0 (25 * ((A • τ : UpperHalfPlane) : ℂ)) =
        μ * Complex.exp (Real.pi * Complex.I *
          (((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) *
            ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (g : ℂ)^2 / 25 -
            ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (g : ℂ))) *
          (-ModularCurve.siegelFun 25
            ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * g) 0 (25 * (τ : ℂ))) := by
  obtain ⟨c, hc⟩ := hA
  let a : ℤ := (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  let b : ℤ := (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  let d : ℤ := (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have hdet : a * d - b * (25 * c) = 1 := by
    have h := A.prop
    rw [Matrix.det_fin_two, hc] at h
    exact h
  let B : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![a, 25*b; c, d], by
      rw [Matrix.det_fin_two]
      change a*d - (25*b)*c = 1
      linear_combination hdet⟩
  obtain ⟨μ, hμ, htrans⟩ := ModularCurve.siegelFun_specialLinearGroup_smul 25 B
  refine ⟨μ, hμ, ?_⟩
  intro g τ
  let τ25 : UpperHalfPlane := ⟨25 * (τ : ℂ), by
    simpa using (mul_pos (by norm_num : (0 : ℝ) < 25) τ.im_pos)⟩
  have hscale : ((B • τ25 : UpperHalfPlane) : ℂ) =
      25 * ((A • τ : UpperHalfPlane) : ℂ) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
    simpa [B, τ25, hc, a, b, d] using
      dilated_fraction (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (τ : ℂ)
  have ht := htrans g 0 τ25
  simp only [zero_mul, add_zero] at ht
  change ModularCurve.siegelFun 25 g 0 ((B • τ25 : UpperHalfPlane) : ℂ) =
    μ * ModularCurve.siegelFun 25 (g*a) (g*(25*b)) (25 * (τ : ℂ)) at ht
  rw [hscale] at ht
  have hs := siegelFun_second_index_shift 25 (a*g) 0 (b*g) (25 * (τ : ℂ))
  norm_num only [Nat.cast_ofNat] at hs
  rw [show g*a = a*g by ring,
    show g*(25*b) = 0 + (b*g)*(25 : ℤ) by ring, hs] at ht
  have he : Real.pi * Complex.I * ((b*g : ℤ) : ℂ) *
      (((a*g : ℤ) : ℂ) - (25 : ℂ)) / (25 : ℂ) =
      Real.pi * Complex.I *
        ((a : ℂ) * (b : ℂ) * (g : ℂ)^2 / 25 - (b : ℂ) * (g : ℂ)) := by
    push_cast
    ring
  rw [he] at ht
  rw [ht]
  ring

end N25
