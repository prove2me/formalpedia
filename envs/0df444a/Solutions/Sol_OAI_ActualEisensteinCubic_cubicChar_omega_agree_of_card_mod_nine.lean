-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_omega_agree_of_card_mod_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:25:28.567458+00:00
-- url     : https://prove2.me/submissions/3b0ac46c-a2fe-4850-8ec6-0e657e6c8a4a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
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
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hP : lambda ∉ P) (hQ : lambda ∉ Q)
    (hcard : Nat.card (O ⧸ P) % 9 = Nat.card (O ⧸ Q) % 9) :
    cubicChar P hP (Ideal.Quotient.mk P omega) =
      cubicChar Q hQ (Ideal.Quotient.mk Q omega) := by
  rw [cubicChar_omega P hP, cubicChar_omega Q hQ]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  have hPpos : 0 < Nat.card (O ⧸ P) := Nat.card_pos
  have hQpos : 0 < Nat.card (O ⧸ Q) := Nat.card_pos
  omega
end OAI.ActualEisensteinCubic
