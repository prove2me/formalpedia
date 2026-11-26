-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.span_range_polynomialFamilyLinearMap_hermiteReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:52.53081+00:00
-- url     : https://prove2.me/submissions/4bb31f87-946a-4711-aa42-35cb34ace793

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_hermiteReal
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_polynomialFamilyLinearMap_of_span_eq_top

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction
variable {M : Type*} [AddCommMonoid M] [Module ℝ M]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (xpow : ℕ → M) :
    Submodule.span ℝ
        (Set.range fun n ↦ polynomialFamilyLinearMap xpow (hermiteReal n)) =
      Submodule.span ℝ (Set.range xpow) := by
  exact span_range_polynomialFamilyLinearMap_of_span_eq_top hermiteReal
    span_range_hermiteReal xpow
end Malliavin.BrownianIteratedConstruction
