-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:37:22.838975+00:00
-- url     : https://prove2.me/submissions/e57dcf88-eb45-4c0e-8338-cb64d7ced8e8

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_pow_three
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_ne_one

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
    (hgood : lambda ∉ P) : orderOf (cubicChar P hgood) = 3 := by
  have hdvd : orderOf (cubicChar P hgood) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (cubicChar_pow_three P hgood)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact False.elim ((cubicChar_ne_one P hgood) (orderOf_eq_one_iff.mp h1))
  · exact h3
end OAI.ActualEisensteinCubic
