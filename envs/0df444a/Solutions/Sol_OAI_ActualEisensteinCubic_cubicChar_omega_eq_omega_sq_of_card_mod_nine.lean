-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_omega_eq_omega_sq_of_card_mod_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:24:26.467721+00:00
-- url     : https://prove2.me/submissions/4af686d0-faf7-4b6f-b46a-5d9c01c72cab

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
    (hcard : Nat.card (O ⧸ P) % 9 = 7) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) = omega ^ 2 := by
  rw [cubicChar_omega P hgood]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  omega
end OAI.ActualEisensteinCubic
