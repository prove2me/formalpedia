-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicGauss_cube_mulShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:43.913931+00:00
-- url     : https://prove2.me/submissions/32484502-ad3b-480d-8be2-037bab2f2aef

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_pow_three

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
theorem _root_.solution {E : Type*} [Field E] (ι : O →+* E)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (ψ : AddChar (O ⧸ P) E) (a : (O ⧸ P)ˣ) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) (ψ.mulShift a) ^ 3 =
      gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let χ := (cubicChar P hgood).ringHomComp ι
  have hχ3 : χ ^ 3 = 1 := by
    change ((cubicChar P hgood).ringHomComp ι) ^ 3 = 1
    rw [MulChar.ringHomComp_pow, cubicChar_pow_three P hgood,
      MulChar.ringHomComp_one]
  have hχinv3 : (χ⁻¹ a) ^ 3 = 1 := by
    have h : (χ⁻¹) ^ 3 = 1 := by rw [inv_pow, hχ3, inv_one]
    rw [← (χ⁻¹).pow_apply_coe, h, MulChar.one_apply_coe]
  change gaussSum χ (ψ.mulShift a) ^ 3 = gaussSum χ ψ ^ 3
  rw [gaussSum_mulShift_eq, mul_pow, hχinv3, one_mul]
end OAI.ActualEisensteinCubic
