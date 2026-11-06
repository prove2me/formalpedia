-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_traceLambda_eq_lambda_of_card_mod_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:06.322088+00:00
-- url     : https://prove2.me/submissions/eda780bb-08c8-4517-915a-291ea41e59bc

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_omega
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_omega_eq_one_of_card_mod_nine
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_traceLambda_relation
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_lambda_eq_one_sub_omega

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
    cubicChar P hgood (Ideal.Quotient.mk P traceLambda) =
      cubicChar P hgood (Ideal.Quotient.mk P lambda) := by
  have hpow : omega ^ ((Nat.card (O ⧸ P) - 1) / 3) = 1 := by
    rw [← cubicChar_omega P hgood]
    exact cubicChar_omega_eq_one_of_card_mod_nine P hgood hcard
  rw [cubicChar_traceLambda_relation P hgood, hpow, one_mul,
    cubicChar_lambda_eq_one_sub_omega P hgood]
end OAI.ActualEisensteinCubic
