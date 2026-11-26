-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.polynomialFamilyLinearMap_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:44.47683+00:00
-- url     : https://prove2.me/submissions/8936d7da-d88f-4a3f-88f5-53223882aeea

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction
variable {M : Type*} [AddCommMonoid M] [Module ℝ M]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (xpow : ℕ → M) (n : ℕ) :
    polynomialFamilyLinearMap xpow (Polynomial.X ^ n) = xpow n := by
  rw [← Polynomial.monomial_one_right_eq_X_pow]
  change ((Polynomial.basisMonomials ℝ).constr ℝ xpow)
    ((Polynomial.basisMonomials ℝ) n) = xpow n
  exact (Polynomial.basisMonomials ℝ).constr_basis ℝ xpow n
end Malliavin.BrownianIteratedConstruction
