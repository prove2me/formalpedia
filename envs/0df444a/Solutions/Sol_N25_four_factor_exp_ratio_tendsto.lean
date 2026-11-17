-- Prove2me | solution 1 for N25.four_factor_exp_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:12.032942+00:00
-- url     : https://prove2.me/submissions/a56c6f4e-46a4-4341-8d4a-2b03291e2327

import Mathlib

set_option autoImplicit false

open Filter Topology

namespace N25

/-- Four normalized nonzero limits determine the normalized limit of their
pair-product quotient, including the exact difference of exponential rates. -/
theorem _root_.solution
    (f : Fin 4 → UpperHalfPlane → ℂ) (r : Fin 4 → ℝ) (c : Fin 4 → ℂ)
    (hc : ∀ j : Fin 4, c j ≠ 0)
    (hl : ∀ j : Fin 4, Filter.Tendsto
      (fun τ : UpperHalfPlane => f j τ /
        Complex.exp (Real.pi*Complex.I*(r j : ℂ)*(τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds (c j))) :
    Filter.Tendsto
      (fun τ : UpperHalfPlane => (f 0 τ*f 1 τ)/(f 2 τ*f 3 τ) /
        Complex.exp (Real.pi*Complex.I*
          ((r 0+r 1-(r 2+r 3) : ℝ) : ℂ)*(τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds ((c 0*c 1)/(c 2*c 3))) := by
  have h := ((hl 0).mul (hl 1)).div ((hl 2).mul (hl 3)) (mul_ne_zero (hc 2) (hc 3))
  apply h.congr'
  filter_upwards [] with τ
  let E (j : Fin 4) : ℂ := Complex.exp (Real.pi*Complex.I*(r j : ℂ)*(τ : ℂ))
  have hE (j : Fin 4) : E j ≠ 0 := Complex.exp_ne_zero _
  have he : Complex.exp (Real.pi*Complex.I*
      ((r 0+r 1-(r 2+r 3) : ℝ) : ℂ)*(τ : ℂ)) = (E 0*E 1)/(E 2*E 3) := by
    dsimp only [E]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  change ((f 0 τ/E 0)*(f 1 τ/E 1))/((f 2 τ/E 2)*(f 3 τ/E 3)) =
    ((f 0 τ*f 1 τ)/(f 2 τ*f 3 τ)) / _
  rw [he]
  by_cases h2 : f 2 τ = 0
  · simp [h2]
  by_cases h3 : f 3 τ = 0
  · simp [h3]
  field_simp [hE 0, hE 1, hE 2, hE 3, h2, h3] <;> ring

end N25
