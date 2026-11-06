-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_omega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:23:15.378699+00:00
-- url     : https://prove2.me/submissions/f190e95f-689d-4826-81f6-5a2ac196e7ce

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_cubic_roots_reduce_injective
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_pow_three
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_reduce


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
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P omega) =
      omega ^ ((Nat.card (O ⧸ P) - 1) / 3) := by
  let χ := cubicChar P hgood
  have hx : (χ (Ideal.Quotient.mk P omega)) ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
    exact MulChar.one_apply ((omega_reduced_primitive P hgood).isUnit (by decide))
  have hy : (omega ^ ((Nat.card (O ⧸ P) - 1) / 3)) ^ 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, omega_primitive.pow_eq_one, one_pow]
  apply cubic_roots_reduce_injective P hgood hx hy
  rw [map_pow]
  exact cubicChar_reduce P hgood (Ideal.Quotient.mk P omega)
end OAI.ActualEisensteinCubic
