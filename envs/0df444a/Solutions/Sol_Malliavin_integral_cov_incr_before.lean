-- Prove2me | solution 1 for Malliavin.integral_cov_incr_before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:16.664799+00:00
-- url     : https://prove2.me/submissions/a43327cb-8c33-4581-a065-737a0d761f04

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral
import Theorems.Thm_Malliavin_integral_cov_sub

set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
variable {W : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hW : IsWienerCov W) {u v x y : ℝ≥0}
    (hyu : y ≤ u) (huv : u ≤ v) (hxy : x ≤ y) :
    ∫ z, (W v z - W u z) * (W y z - W x z) = 0 := by
  have hyv : y ≤ v := hyu.trans huv
  have hxv : x ≤ v := hxy.trans hyv
  have hxu : x ≤ u := hxy.trans hyu
  rw [integral_cov_sub hW, min_eq_right hyv, min_eq_right hxv, min_eq_right hyu,
    min_eq_right hxu]
  ring
end Malliavin
