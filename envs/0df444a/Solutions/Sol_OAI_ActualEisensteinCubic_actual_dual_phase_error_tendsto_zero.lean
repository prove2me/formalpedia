-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.actual_dual_phase_error_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:46:57.460531+00:00
-- url     : https://prove2.me/submissions/a756b6c5-b3f6-4e83-a1bc-ebaf65e488c6

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Theorems.Thm_OAI_ActualEisensteinCubic_actual_variable_kernel_eq_dualVarTerm
import Theorems.Thm_OAI_ActualEisensteinCubic_actual_fixed_kernel_eq_dualFixedTerm_point
import Theorems.Thm_OAI_ActualEisensteinCubic_coordinate_norm_pos_of_nonzero
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_OscSpecial_normalized_dual_phase_sum_error_tendsto_zero
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
open EisensteinEmbedding ConcreteTraceCRT Complex
open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped Topology
open Filter
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    Tendsto
      (fun η : ℝ => η * ‖
        (∑' y : O, actualVariableDualKernel a b η y) -
        (∑' y : O, actualFixedDualKernel a b η y)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      simpa only [pow_two] using hqZ)
  have hbase := OscSpecial.normalized_dual_phase_sum_error_tendsto_zero hq
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  change 0 < η at hη
  have hvar :
      (∑' y : O, actualVariableDualKernel a b η y) =
        ∑' z : ℤ × ℤ, OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by
    calc
      (∑' y : O, actualVariableDualKernel a b η y) =
          ∑' z : ℤ × ℤ,
            actualVariableDualKernel a b η (dualFrequencyEquiv z) :=
        (dualFrequencyEquiv.tsum_eq (actualVariableDualKernel a b η)).symm
      _ = _ := by
        apply tsum_congr
        intro z
        exact actual_variable_kernel_eq_dualVarTerm a b hc η hη z
  have hfixed :
      (∑' y : O, actualFixedDualKernel a b η y) =
        ∑' z : ℤ × ℤ, OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z := by
    calc
      (∑' y : O, actualFixedDualKernel a b η y) =
          ∑' z : ℤ × ℤ,
            actualFixedDualKernel a b η (dualFrequencyEquiv z) :=
        (dualFrequencyEquiv.tsum_eq (actualFixedDualKernel a b η)).symm
      _ = _ := by
        apply tsum_congr
        intro z
        exact actual_fixed_kernel_eq_dualFixedTerm_point a b η z
  rw [hvar, hfixed]
end OAI.ActualEisensteinCubic
