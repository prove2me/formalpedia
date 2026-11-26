-- Prove2me | solution 1 for Malliavin.coeFn_iteratedKernelPurePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:42.023445+00:00
-- url     : https://prove2.me/submissions/a38f21cc-6ecd-4720-b6fd-ff0d59b66ea9

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_Malliavin_IteratedKernelPurePower

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
namespace Malliavin
theorem _root_.solution (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (iteratedKernelPurePower n f : (Fin n → ℝ≥0) → ℝ) =ᵐ[iteratedKernelMeasure n]
      iteratedKernelPurePowerFun n f := by
  exact MemLp.coeFn_toLp _
end Malliavin
