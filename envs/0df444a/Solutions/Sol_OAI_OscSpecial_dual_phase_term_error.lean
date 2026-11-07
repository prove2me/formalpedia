-- Prove2me | solution 1 for OAI.OscSpecial.dual_phase_term_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:38.045255+00:00
-- url     : https://prove2.me/submissions/10143e17-2d72-41bf-bdc9-382140abd18e

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Theorems.Thm_OAI_GaussianPhasePointwise_exp_imag_denominator_error
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_OscSpecial_quadratic_phase_abs_le
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace OscSpecial
private theorem phaseAngle_bound (a b : ℝ) (z : ℤ × ℤ) :
    |phaseAngle a b z| ≤
      (Real.pi / 2) * phaseBoundConstant a b * dualQ z := by
  have h := quadratic_phase_abs_le a b (z.1 : ℝ) (z.2 : ℝ)
  dsimp [phaseAngle, dualTrace, dualQ]
  rw [abs_mul, abs_neg, abs_of_pos (half_pos Real.pi_pos)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left h (half_pos Real.pi_pos).le
private theorem r_eq_one_add_phaseA (η a b : ℝ) :
    r η a b = 1 + phaseA a b * η ^ 2 := by
  unfold r phaseA
  ring
private theorem phaseA_nonneg {a b : ℝ} (hq : 0 ≤ q a b) :
    0 ≤ phaseA a b := by
  unfold phaseA
  positivity
open scoped Topology
open Filter
end OscSpecial
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT
end ActualEisensteinCubic
open Filter
open scoped Topology
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
end
end OAI
end

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
open OAI.OscSpecial
namespace OAI.OscSpecial
theorem _root_.solution {η a b : ℝ} (_hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
      dualAmp η a b z *
        ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
        (phaseA a b * η ^ 2) := by
  have hA : 0 ≤ phaseA a b := phaseA_nonneg hq.le
  have hamp : 0 ≤ dualAmp η a b z := (Real.exp_pos _).le
  have hphase := GaussianPhasePointwise.exp_imag_denominator_error
    (phaseAngle a b z) (phaseA a b) η hA
  rw [← r_eq_one_add_phaseA η a b] at hphase
  have hangle := phaseAngle_bound a b z
  have hangle' := mul_le_mul_of_nonneg_right hangle
    (mul_nonneg hA (sq_nonneg η))
  dsimp [dualVarTerm, dualFixedTerm]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hamp]
  nlinarith [mul_le_mul_of_nonneg_left hphase hamp,
    mul_le_mul_of_nonneg_left hangle' hamp]
end OAI.OscSpecial
