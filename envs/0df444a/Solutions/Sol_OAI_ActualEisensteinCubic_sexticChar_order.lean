-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.sexticChar_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:37:30.780422+00:00
-- url     : https://prove2.me/submissions/b8ea8b1f-0e5a-469e-a01a-f0cfbc26121f

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_ne_one
import Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_powers
import Theorems.Thm_OAI_ActualEisensteinCubic_quadraticCharO_ne_one

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
    orderOf (sexticChar P hgood) = 6 := by
  have h2 := (sexticChar_powers P hgood).1
  have h3 := (sexticChar_powers P hgood).2.1
  have h6 := (sexticChar_powers P hgood).2.2
  have hdiv : orderOf (sexticChar P hgood) ∣ 6 :=
    orderOf_dvd_of_pow_eq_one h6
  have hne2 : orderOf (sexticChar P hgood) ≠ 2 := by
    intro he
    have hχ2 := pow_orderOf_eq_one (sexticChar P hgood)
    rw [he, h2] at hχ2
    exact cubicChar_ne_one P hgood hχ2
  have hne3 : orderOf (sexticChar P hgood) ≠ 3 := by
    intro he
    have hχ3 := pow_orderOf_eq_one (sexticChar P hgood)
    rw [he, h3] at hχ3
    exact quadraticCharO_ne_one P hchar hχ3
  have hne1 : orderOf (sexticChar P hgood) ≠ 1 := by
    intro he
    have hχ1 := orderOf_eq_one_iff.mp he
    rw [hχ1] at h2
    exact cubicChar_ne_one P hgood (by simpa using h2.symm)
  have hne0 : orderOf (sexticChar P hgood) ≠ 0 := by
    intro he
    norm_num [he] at hdiv
  have hpos : 0 < orderOf (sexticChar P hgood) := Nat.pos_of_ne_zero hne0
  have hle : orderOf (sexticChar P hgood) ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
  have hne4 : orderOf (sexticChar P hgood) ≠ 4 := by
    intro he
    norm_num [he] at hdiv
  have hne5 : orderOf (sexticChar P hgood) ≠ 5 := by
    intro he
    norm_num [he] at hdiv
  omega
end OAI.ActualEisensteinCubic
