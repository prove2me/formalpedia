-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.sexticChar_powers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:31.529625+00:00
-- url     : https://prove2.me/submissions/3adecd03-5d3c-4406-9579-e782f14b1189

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_pow_three
import Theorems.Thm_OAI_ActualEisensteinCubic_quadraticCharO_sq

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
    (hgood : lambda ∉ P) :
    sexticChar P hgood ^ 2 = cubicChar P hgood ∧
    sexticChar P hgood ^ 3 = quadraticCharO P ∧
    sexticChar P hgood ^ 6 = 1 := by
  have hc := cubicChar_pow_three P hgood
  have hq := quadraticCharO_sq P
  let c := cubicChar P hgood
  let q := quadraticCharO P
  have htwo : (c ^ 2 * q) ^ 2 = c := by
    calc
      (c ^ 2 * q) ^ 2 = c ^ 4 * q ^ 2 := by rw [mul_pow, ← pow_mul]
      _ = c := by rw [hq]; calc
        c ^ 4 * 1 = c ^ 3 * c := by group
        _ = c := by rw [hc, one_mul]
  have hthree : (c ^ 2 * q) ^ 3 = q := by
    calc
      (c ^ 2 * q) ^ 3 = (c ^ 3) ^ 2 * (q ^ 2) * q := by simp [mul_pow]; group
      _ = q := by rw [hc, hq]; group
  refine ⟨htwo, hthree, ?_⟩
  calc
    (c ^ 2 * q) ^ 6 = ((c ^ 2 * q) ^ 3) ^ 2 := by group
    _ = 1 := by rw [hthree, hq]
end OAI.ActualEisensteinCubic
