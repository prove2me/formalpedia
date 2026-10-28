-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_on_ideal_power_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T18:49:50.682732+00:00
-- url     : https://prove2.me/submissions/87053b41-dd51-4722-928d-8c12bbf3e353

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_mem_ideal_pow_sum_products
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_coeff_vanish_of_sum_products

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    {m : Nat} (v : Fin (m + 1) -> Real) (R : Real) (n : Nat) (hn : 0 < n)
    (hv : forall i, 0 < v i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (phi : RingHom (MvPolynomial (Fin (m + 1)) Complex)
      (MvPowerSeries (Fin (m + 1)) Complex))
    (hcoeff : forall (Q : MvPolynomial (Fin (m + 1)) Complex), Membership.mem I Q ->
      forall (a : Fin (m + 1) -> Nat),
        Finset.sum Finset.univ (fun i => v i * (a i : Real)) < R ->
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (phi Q) = 0)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : Membership.mem (I ^ n) P)
    (a : Fin (m + 1) -> Nat)
    (ha : Finset.sum Finset.univ (fun i => v i * (a i : Real)) < (n : Real) * R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (phi P) = 0 := by
  have hdecomp :=
    OAI.PiExponent.LogarithmicJetIdeals.mem_ideal_pow_sum_products I n P hP
  let s := Classical.choose hdecomp
  have hs := (Classical.choose_spec hdecomp).1
  have hmem := (Classical.choose_spec hdecomp).2
  exact OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_sum_products
    v R n hn hv phi I hcoeff P s hs hmem a ha
