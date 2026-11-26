-- Prove2me | solution 1 for Malliavin.norm_iteratedKernelPurePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:23.760277+00:00
-- url     : https://prove2.me/submissions/0cc7c595-fc87-4ad4-b91b-f8132956e119

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_Malliavin_IteratedKernelPurePower
import Theorems.Thm_Malliavin_norm_sq_iteratedKernelPurePower

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
namespace Malliavin
theorem _root_.solution (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖iteratedKernelPurePower n f‖ = ‖f‖ ^ n := by
  apply (sq_eq_sq₀ (norm_nonneg _) (pow_nonneg (norm_nonneg _) n)).mp
  rw [norm_sq_iteratedKernelPurePower]
  calc
    (‖f‖ ^ 2) ^ n = ‖f‖ ^ (2 * n) := (pow_mul ‖f‖ 2 n).symm
    _ = ‖f‖ ^ (n * 2) := by rw [Nat.mul_comm 2 n]
    _ = (‖f‖ ^ n) ^ 2 := pow_mul ‖f‖ n 2
end Malliavin
