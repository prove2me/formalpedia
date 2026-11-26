-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.span_range_hermiteReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:04.316222+00:00
-- url     : https://prove2.me/submissions/e1f69f04-7d43-49ea-81f0-3c833353f01b

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_hermiteReal_isMonicOfDegree
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_eq_top_of_isMonicOfDegree

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution :
    Submodule.span ℝ (Set.range hermiteReal) = ⊤ := by
  exact span_range_eq_top_of_isMonicOfDegree hermiteReal hermiteReal_isMonicOfDegree
end Malliavin.BrownianIteratedConstruction
