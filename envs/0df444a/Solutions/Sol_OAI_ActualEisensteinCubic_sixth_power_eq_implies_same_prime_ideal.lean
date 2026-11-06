-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.sixth_power_eq_implies_same_prime_ideal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:14.355583+00:00
-- url     : https://prove2.me/submissions/522e85fa-e77b-4f51-808e-4478afc6dd38

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace

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
    (p q : O)
    (hp : (Ideal.span {p} : Ideal O).IsMaximal)
    (hq : (Ideal.span {q} : Ideal O).IsMaximal)
    (h : p ^ 6 = q ^ 6) :
    (Ideal.span {p} : Ideal O) = Ideal.span {q} := by
  have hq6 : q ^ 6 ∈ Ideal.span {q} :=
    Ideal.mem_span_singleton.mpr (dvd_pow_self q (by decide))
  have hp6 : p ^ 6 ∈ Ideal.span {q} := by rw [h]; exact hq6
  have hpmem : p ∈ Ideal.span {q} :=
    hq.isPrime.mem_of_pow_mem 6 hp6
  have hle : (Ideal.span {p} : Ideal O) ≤ Ideal.span {q} :=
    (Ideal.span_singleton_le_iff_mem _).mpr hpmem
  exact hp.eq_of_le hq.ne_top hle
end OAI.ActualEisensteinCubic
