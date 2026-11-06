-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubic_roots_reduce_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:25.965257+00:00
-- url     : https://prove2.me/submissions/830c06c5-4568-4e29-9b81-2782f5f46c4a

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
    (hgood : lambda ∉ P) {x y : O}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one hx
  obtain ⟨j, hj, rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one hy
  have hij : i = j := by
    apply (omega_reduced_primitive P hgood).pow_inj hi hj
    simpa only [map_pow] using hxy
  rw [hij]
end OAI.ActualEisensteinCubic
