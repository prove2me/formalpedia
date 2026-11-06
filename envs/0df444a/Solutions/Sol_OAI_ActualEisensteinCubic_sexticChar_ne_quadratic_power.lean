-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.sexticChar_ne_quadratic_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:44.503387+00:00
-- url     : https://prove2.me/submissions/26ec17d3-8d7a-49e4-ba7b-3a3c72d7597b

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_order

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
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    sexticChar P hgood ≠ (sexticChar P hgood) ^ 3 := by
  intro h
  have htwo : (sexticChar P hgood) ^ 2 = 1 := by
    calc
      (sexticChar P hgood) ^ 2 =
          (sexticChar P hgood) ^ 3 * (sexticChar P hgood)⁻¹ := by group
      _ = 1 := by rw [← h]; group
  have hdiv : orderOf (sexticChar P hgood) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one htwo
  rw [sexticChar_order P hgood hchar] at hdiv
  norm_num at hdiv
end OAI.ActualEisensteinCubic
