-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_omega_eq_omega_of_card_mod_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:24:25.35895+00:00
-- url     : https://prove2.me/submissions/033cffa7-1ed9-4753-9018-9f38545fefd6

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_omega

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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (hcard : Nat.card (O ⧸ P) % 9 = 4) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) = omega := by
  rw [cubicChar_omega P hgood]
  calc
    omega ^ ((Nat.card (O ⧸ P) - 1) / 3) = omega ^ 1 := by
      apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
      rw [← omega_primitive.eq_orderOf]
      omega
    _ = omega := pow_one omega
end OAI.ActualEisensteinCubic
