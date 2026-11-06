-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_reduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:31.416961+00:00
-- url     : https://prove2.me/submissions/ead0800f-9d9c-4ea4-b2f2-6f576574ae60

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualCubicChar_cubicResidueChar_reduce_unit

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
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    (Ideal.Quotient.mk P) (cubicChar P hgood x) =
      x ^ ((Nat.card (O ⧸ P) - 1) / 3) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 0 < m := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  rw [Nat.card_eq_fintype_card]
  change (Ideal.Quotient.mk P)
      (ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
        omega_primitive (omega_reduced_primitive P hgood) m hq x) = x ^ m
  by_cases hx : x = 0
  · subst x
    rw [(ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
      omega_primitive (omega_reduced_primitive P hgood) m hq).map_zero,
      map_zero, zero_pow hm.ne']
  · let u : (O ⧸ P)ˣ := (isUnit_iff_ne_zero.mpr hx).unit
    have hu : (u : O ⧸ P) = x := (isUnit_iff_ne_zero.mpr hx).unit_spec
    rw [← hu]
    exact ActualCubicChar.cubicResidueChar_reduce_unit
      (Ideal.Quotient.mk P) omega omega_primitive
      (omega_reduced_primitive P hgood) m hq u
end OAI.ActualEisensteinCubic
