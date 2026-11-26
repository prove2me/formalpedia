-- Prove2me | solution 1 for Malliavin.integral_cov_incr_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:48.483277+00:00
-- url     : https://prove2.me/submissions/b9e7389e-1b16-47c8-b5b3-3ce9a6e01fc7

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral
import Theorems.Thm_Malliavin_integral_cov_sub
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
variable {W : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hW : IsWienerCov W) {u v : ℝ≥0} (huv : u ≤ v) :
    ∫ z, (W v z - W u z) * (W v z - W u z) = (v : ℝ) - (u : ℝ) := by
  rw [integral_cov_sub hW]
  simp only [min_self, min_eq_left huv, min_eq_right huv]
  ring
end Malliavin
