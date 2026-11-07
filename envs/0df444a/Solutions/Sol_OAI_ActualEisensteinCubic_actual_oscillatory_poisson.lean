-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.actual_oscillatory_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:30:30.336421+00:00
-- url     : https://prove2.me/submissions/6b1d761c-e5cf-424b-812a-638e22c3dad0

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_OscSpecial_oscillatory_gaussian_poisson
import Theorems.Thm_OAI_ActualEisensteinCubic_actual_oscillatory_sum_eq_binary
import Theorems.Thm_OAI_ActualEisensteinCubic_dual_gaussian_is_actual_trace_phase
import Theorems.Thm_OAI_ActualEisensteinCubic_coordinate_norm_pos_of_nonzero
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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let r : ℝ := OscSpecial.r η (a : ℝ) (b : ℝ)
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      (1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' y : O,
          Complex.exp (-(Real.pi : ℂ) *
            ((η : ℂ) * (q : ℂ) / (4 * (r : ℂ))) *
            (‖eisEmbedding y‖ ^ 2 : ℂ)) *
          ShortDraftTrace.breveE
            (eisEmbedding (-(c * y^2)) / eisLam / ((4*r : ℝ) : ℂ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  dsimp only
  rw [actual_oscillatory_sum_eq_binary a b hc η,
    OscSpecial.oscillatory_gaussian_poisson hη hq]
  congr 1
  let W : O → ℂ := fun y =>
    Complex.exp (-(Real.pi : ℂ) *
      ((η : ℂ) * (OscSpecial.q (a : ℝ) (b : ℝ) : ℂ) /
        (4 * (OscSpecial.r η (a : ℝ) (b : ℝ) : ℂ))) *
      (‖eisEmbedding y‖ ^ 2 : ℂ)) *
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b * y^2)) /
        eisLam /
        ((4 * OscSpecial.r η (a : ℝ) (b : ℝ) : ℝ) : ℂ))
  calc
    (∑' p : ℤ × ℤ,
      RankTwoComplex.dualGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) p) =
        ∑' p : ℤ × ℤ, W (dualFrequencyEquiv p) := by
      apply tsum_congr
      intro p
      simpa only [W] using
        dual_gaussian_is_actual_trace_phase a b p.1 p.2 hc η hη
    _ = ∑' y : O, W y := dualFrequencyEquiv.tsum_eq W
end OAI.ActualEisensteinCubic
