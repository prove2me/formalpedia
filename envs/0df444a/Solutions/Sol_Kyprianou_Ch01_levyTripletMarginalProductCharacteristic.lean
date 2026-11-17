-- Prove2me | solution 1 for Kyprianou.Ch01.levyTripletMarginalProductCharacteristic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:02:47.277538+00:00
-- url     : https://prove2.me/submissions/698323c9-0e02-45a7-a917-acb1d9c392a9

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Theorems.Thm_Kyprianou_Ch01_levyTripleExponent_expGaussianFactorisation
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) (t : ℝ≥0)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : ∀ xi : ℝ,
      charFun mu xi = Complex.exp (((t : ℝ) : ℂ) *
        levyTripleExponent
          ⟨T.drift, 0, T.levyMeasure, T.levyMeasure_isLevyMeasure⟩ xi))
    (xi : ℝ) :
    charFun ((mu.prod (gaussianReal 0 (t * T.gaussianVariance))).map
      (fun p : ℝ × ℝ => p.1 + p.2)) xi =
      Complex.exp (((t : ℝ) : ℂ) * levyTripleExponent T xi) := by
  rw [ProbabilityTheory.charFun_map_add_prod_eq_mul]
  simp only [Pi.mul_apply]
  rw [hmu, ProbabilityTheory.charFun_gaussianReal]
  have hfactor :=
    (Kyprianou.Ch01.levyTripleExponent_expGaussianFactorisation T t xi).symm
  convert hfactor using 1
  congr 1 <;> push_cast <;> ring
