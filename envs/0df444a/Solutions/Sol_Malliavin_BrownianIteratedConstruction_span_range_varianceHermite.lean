-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.span_range_varianceHermite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:26.987907+00:00
-- url     : https://prove2.me/submissions/60cad69c-29ef-43c7-9051-25a124f30c80

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_eq_top_of_isMonicOfDegree
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_varianceHermite_isMonicOfDegree

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (variance : ℝ) :
    Submodule.span ℝ (Set.range (varianceHermite variance)) = ⊤ := by
  exact span_range_eq_top_of_isMonicOfDegree (varianceHermite variance)
    (varianceHermite_isMonicOfDegree variance)
end Malliavin.BrownianIteratedConstruction
