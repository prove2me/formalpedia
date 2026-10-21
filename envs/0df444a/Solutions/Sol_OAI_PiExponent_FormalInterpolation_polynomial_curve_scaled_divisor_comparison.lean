-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomial_curve_scaled_divisor_comparison
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:37:02.30646+00:00
-- url     : https://prove2.me/submissions/98030e27-b025-4c23-8e42-a29362a4a589
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomial_curve_zero_divisor_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomial_curve_mass_le_zero_divisor

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (E : Type) [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin d → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (N : Real) (hN : 0 ≤ N)
    (F : MvPolynomial (Fin d) Complex)
    (hF : logarithmicDegreeBound w N F)
    (hne : MvPolynomial.aeval x F ≠ 0)
    (a r : Real) (ha : 0 < a) (hr : 0 < r)
    (b : PolynomialCurvePlace E → Real) (hb : ∀ nu, 0 ≤ b nu)
    (hlocal : ∀ nu, 0 < b nu →
      a * b nu ≤ r * (polynomialCurveOrder nu (MvPolynomial.aeval x F) : Real)) :
    a * (∑ᶠ nu : PolynomialCurvePlace E, b nu) ≤
      r * N * (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) := by
  have hdiv :=
    OAI.PiExponent.FormalInterpolation.polynomial_curve_zero_divisor_bound
      E htrdeg x hgen w hw N hN F hF hne
  have hmass :=
    OAI.PiExponent.FormalInterpolation.polynomial_curve_mass_le_zero_divisor
      (MvPolynomial.aeval x F) a r ha hr b hb hlocal hdiv.1
  calc
    a * (∑ᶠ nu : PolynomialCurvePlace E, b nu) ≤
        r * (∑ᶠ nu : PolynomialCurvePlace E,
          max (polynomialCurveOrder nu (MvPolynomial.aeval x F) : Real) 0) := hmass
    _ ≤ r * (N * (∑ᶠ nu : PolynomialCurvePlace E,
          polynomialCurvePole nu x w)) :=
      mul_le_mul_of_nonneg_left hdiv.2 (le_of_lt hr)
    _ = r * N * (∑ᶠ nu : PolynomialCurvePlace E,
          polynomialCurvePole nu x w) := by ring
