-- Prove2me | solution 1 for Malliavin.integral_cov_incr_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:20.865447+00:00
-- url     : https://prove2.me/submissions/92df63cd-730d-4c99-b065-23c6ca46bb5d

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
    (huv : u ≤ v) (hvx : v ≤ x) (hxy : x ≤ y) :
    ∫ z, (W v z - W u z) * (W y z - W x z) = 0 := by
  have hyv : v ≤ y := hvx.trans hxy
  have huy : u ≤ y := huv.trans hyv
  have hux : u ≤ x := huv.trans hvx
  rw [integral_cov_sub hW, min_eq_left hyv, min_eq_left hvx, min_eq_left huy,
    min_eq_left hux]
  ring
end Malliavin
