-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_omega_eq_one_of_card_mod_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:24:23.349247+00:00
-- url     : https://prove2.me/submissions/fd7b117b-0f7a-42c1-a224-a97fe911710b

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
    (hcard : Nat.card (O ⧸ P) % 9 = 1) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) = 1 := by
  rw [cubicChar_omega P hgood]
  apply (omega_primitive.pow_eq_one_iff_dvd _).mpr
  omega
end OAI.ActualEisensteinCubic
