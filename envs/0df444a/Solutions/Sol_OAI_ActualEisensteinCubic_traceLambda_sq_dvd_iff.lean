-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.traceLambda_sq_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:27:46.49421+00:00
-- url     : https://prove2.me/submissions/0285982d-8ce2-417d-8ec4-0f6bb73d2a69

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

theorem solution (x : O) :
    traceLambda ^ 2 ∣ x ↔ lambda ^ 2 ∣ x := by
  have h : Associated traceLambda lambda := by
    rw [traceLambda_eq_unit_mul_lambda]
    exact associated_unit_mul_left lambda (-omega) neg_omega_isUnit
  exact h.pow_pow.dvd_iff_dvd_left
