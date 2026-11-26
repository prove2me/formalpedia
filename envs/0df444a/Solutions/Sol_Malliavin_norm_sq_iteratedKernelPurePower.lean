-- Prove2me | solution 1 for Malliavin.norm_sq_iteratedKernelPurePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:23:50.463499+00:00
-- url     : https://prove2.me/submissions/ad690c9d-26a9-465e-9ff6-a75e965ad2e4

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_Malliavin_IteratedKernelPurePower
import Theorems.Thm_Malliavin_inner_iteratedKernelPurePower

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
namespace Malliavin
theorem _root_.solution (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖iteratedKernelPurePower n f‖ ^ 2 = (‖f‖ ^ 2) ^ n := by
  rw [← real_inner_self_eq_norm_sq, inner_iteratedKernelPurePower,
    real_inner_self_eq_norm_sq]
end Malliavin
