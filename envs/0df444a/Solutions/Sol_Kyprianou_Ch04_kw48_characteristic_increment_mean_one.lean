-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_characteristic_increment_mean_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:31:52.766007+00:00
-- url     : https://prove2.me/submissions/46a25963-1fcd-4670-adf3-92a6f70e9dd6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The normalised complex future increment has expectation one. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ w, Complex.exp (Complex.I * (theta : Complex) *
        (L.X t w : Complex)) ∂P) =
      Complex.exp (-((t : Real) : Complex) * Psi theta))
    (alpha : Real) (s t : NNReal) (hst : s ≤ t) :
    (∫ w, Complex.exp
      (Complex.I * (alpha : Complex) * ((L.X t w-L.X s w : Real) : Complex) +
        (((t-s : NNReal) : Real) : Complex) * Psi alpha) ∂P) = 1 := by
  let phi : Real → Complex := fun z =>
    Complex.exp (Complex.I * (alpha : Complex) * (z : Complex))
  have hm : Measurable phi := by
    unfold phi
    fun_prop
  have hI := ((L.stationaryIncrements s t hst).comp hm).integral_eq
  change (∫ w, phi (L.X t w-L.X s w) ∂P) =
    ∫ w, phi (L.X (t-s) w) ∂P at hI
  rw [show (∫ w, Complex.exp
      (Complex.I * (alpha : Complex) * ((L.X t w-L.X s w : Real) : Complex) +
        (((t-s : NNReal) : Real) : Complex) * Psi alpha) ∂P) =
    (∫ w, phi (L.X t w-L.X s w) ∂P) *
      Complex.exp ((((t-s : NNReal) : Real) : Complex) * Psi alpha) by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [phi,Complex.exp_add]]
  rw [hI]
  unfold phi
  rw [hPsi, ← Complex.exp_add]
  simp
