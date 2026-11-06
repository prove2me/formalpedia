-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.sixth_power_rows_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:23:26.038981+00:00
-- url     : https://prove2.me/submissions/f5c1c912-c243-47a3-91a3-a84392e9125c

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_sixth_power_eq_implies_same_prime_ideal

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
    {ι : Type*} (S : Finset ι) (P : ι → Ideal O) (p : ι → O)
    (hprime : ∀ i ∈ S, (P i).IsMaximal)
    (hgen : ∀ i ∈ S, P i = Ideal.span {p i})
    (hinj : Set.InjOn P (S : Set ι)) :
    Set.InjOn (fun i => p i ^ 6) (S : Set ι) := by
  intro i hi j hj heq
  have hsame : Ideal.span {p i} = (Ideal.span {p j} : Ideal O) :=
    sixth_power_eq_implies_same_prime_ideal (p i) (p j)
      (hgen i hi ▸ hprime i hi)
      (hgen j hj ▸ hprime j hj) heq
  apply hinj hi hj
  rw [hgen i hi, hgen j hj]
  exact hsame
end OAI.ActualEisensteinCubic
