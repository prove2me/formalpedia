-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.full_dual_abel_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:45:21.948493+00:00
-- url     : https://prove2.me/submissions/c5af41a9-6379-436b-bd4e-8f50c7d2c7a8

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Theorems.Thm_OAI_ActualEisensteinCubic_dual_abel_coefficient
import Theorems.Thm_OAI_ActualEisensteinCubic_coordinate_norm_pos_of_nonzero
import Theorems.Thm_OAI_ActualEisensteinCubic_osc_q_eq_eis_norm_sq
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((Real.sqrt q / 2 : ℝ) : ℂ) *
      (((4 / q : ℝ) : ℂ) *
        ((2 / (Real.sqrt 3 *
          (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ))) =
      (((2 / (Real.sqrt 3 * ‖ConcreteTraceCRT.eisEmbedding c‖) : ℝ) : ℂ) / 2) := by
  dsimp only
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  rw [dual_abel_coefficient a b hq]
  have hqnorm := osc_q_eq_eis_norm_sq a b
  have hsqrt : Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) =
      ‖ConcreteTraceCRT.eisEmbedding
        (ActualEisensteinCoordinates.eval a b)‖ := by
    rw [hqnorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hsqrt, hqnorm]
  have hn : (‖ConcreteTraceCRT.eisEmbedding
      (ActualEisensteinCoordinates.eval a b)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (norm_pos_iff.mpr
      (ConcreteTraceCRT.eisEmbedding_ne_zero hc)))
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  push_cast
  field_simp [hn, hs]
end OAI.ActualEisensteinCubic
