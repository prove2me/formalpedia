-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_pow_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:41.626616+00:00
-- url     : https://prove2.me/submissions/742825f3-168d-42ac-977d-dae1b8409f88

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualCubicChar_cubicResidueChar_pow_three

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
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : cubicChar P hgood ^ 3 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  change ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq ^ 3 = 1
  exact ActualCubicChar.cubicResidueChar_pow_three
    (Ideal.Quotient.mk P) omega omega_primitive
    (omega_reduced_primitive P hgood) m hq
end OAI.ActualEisensteinCubic
