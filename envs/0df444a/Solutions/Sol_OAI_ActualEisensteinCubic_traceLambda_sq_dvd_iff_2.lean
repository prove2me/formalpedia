-- Prove2me | solution 2 for OAI.ActualEisensteinCubic.traceLambda_sq_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:34:44.587203+00:00
-- url     : https://prove2.me/submissions/e7155820-79b4-4ed4-a0b4-d46fbbe8d20d

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier

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
open OAI.ActualEisensteinCubic
open NumberField
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (x : O) :
    traceLambda ^ 2 ∣ x ↔ lambda ^ 2 ∣ x := by
  rw [traceLambda_eq_unit_mul_lambda, mul_pow]
  exact (neg_omega_isUnit.pow 2).mul_left_dvd
end OAI.ActualEisensteinCubic
