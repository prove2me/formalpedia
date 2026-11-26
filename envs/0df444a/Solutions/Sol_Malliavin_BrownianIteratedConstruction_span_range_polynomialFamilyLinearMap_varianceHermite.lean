-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.span_range_polynomialFamilyLinearMap_varianceHermite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:44.17295+00:00
-- url     : https://prove2.me/submissions/252d1303-00e9-406c-b406-69dcd1889665

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_varianceHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_polynomialFamilyLinearMap_of_span_eq_top

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction
variable {M : Type*} [AddCommMonoid M] [Module ℝ M]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (variance : ℝ) (xpow : ℕ → M) :
    Submodule.span ℝ
        (Set.range fun n ↦ polynomialFamilyLinearMap xpow (varianceHermite variance n)) =
      Submodule.span ℝ (Set.range xpow) := by
  exact span_range_polynomialFamilyLinearMap_of_span_eq_top
    (varianceHermite variance) (span_range_varianceHermite variance) xpow
end Malliavin.BrownianIteratedConstruction
