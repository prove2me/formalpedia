-- Prove2me | solution 1 for N25.unitNumerator25_bounded_product
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:47.057193+00:00
-- url     : https://prove2.me/submissions/efa790f8-d9d6-46a9-b244-e90bbbd1ac49

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_unitAnalytic25_cusp_leading_limit
import Theorems.Thm_N25_discriminant_normalized_tendsto_one
import Theorems.Thm_N25_bounded_of_nonnegative_exp

set_option autoImplicit false

open Filter Topology

namespace N25

/-- The cube of the discriminant cancels the worst transformed-unit
exponent, giving the actual numerator product a finite cusp bound. -/
theorem _root_.solution
    (i : Fin 5) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : UpperHalfPlane => ModularForm.discriminant τ ^ 3 *
        unitAnalytic25 i (A • τ)) := by
  obtain ⟨ℓ, hℓ, c, _, hl⟩ := unitAnalytic25_cusp_leading_limit i A
  let f (τ : UpperHalfPlane) : ℂ := ModularForm.discriminant τ ^ 3 * unitAnalytic25 i (A • τ)
  have ht := (discriminant_normalized_tendsto_one.pow 3).mul hl
  norm_num only [one_pow, one_mul] at ht
  have H : Tendsto
      (fun τ : UpperHalfPlane => f τ /
        Complex.exp (2*Real.pi*Complex.I*((ℓ+3 : ℝ) : ℂ)*(τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds c) := by
    apply ht.congr'
    filter_upwards [] with τ
    have he : Complex.exp (2*Real.pi*Complex.I*((ℓ+3 : ℝ) : ℂ)*(τ : ℂ)) =
        (Complex.exp (2*Real.pi*Complex.I*(τ : ℂ)))^3 *
          Complex.exp (2*Real.pi*Complex.I*(ℓ : ℂ)*(τ : ℂ)) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    change (ModularForm.discriminant τ / Complex.exp (2*Real.pi*Complex.I*(τ : ℂ)))^3 *
        (unitAnalytic25 i (A • τ) / Complex.exp (2*Real.pi*Complex.I*(ℓ : ℂ)*(τ : ℂ))) =
      f τ / _
    rw [he]
    dsimp only [f]
    field_simp [Complex.exp_ne_zero] <;> ring
  exact bounded_of_nonnegative_exp f (ℓ+3) (by linarith) c H

end N25
