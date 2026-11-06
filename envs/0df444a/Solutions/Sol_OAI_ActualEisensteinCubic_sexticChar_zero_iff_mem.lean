-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.sexticChar_zero_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:04.501536+00:00
-- url     : https://prove2.me/submissions/fc9cb8df-9c62-4246-be51-886d60f381d4

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
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (a : O) :
    sexticChar P hgood (Ideal.Quotient.mk P a) = 0 ↔ a ∈ P := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  rw [MulChar.apply_eq_zero_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using
    (Ideal.Quotient.eq_zero_iff_mem (I := P) (a := a))
end OAI.ActualEisensteinCubic
