-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.ideal_pow_product_mem
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:53:54.540889+00:00
-- url     : https://prove2.me/submissions/6ffa3e7e-70bd-4a97-b237-40ba9dcd6e82

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
open scoped BigOperators

theorem solution {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex)) (s m : Nat)
    (v : Fin m → MvPolynomial (Fin d) Complex)
    (hv : ∀ i, v i ∈ I ^ s) :
    (∏ i, v i) ∈ I ^ (s * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hp : I ^ s * I ^ (s * m) = I ^ (s * (m + 1)) := by
        rw [← Ideal.IsTwoSided.pow_add]
        rw [Nat.mul_succ, Nat.add_comm s (s * m)]
      rw [Fin.prod_univ_succ, ← hp]
      exact Ideal.mul_mem_mul (hv 0) (ih (fun i => v i.succ) (fun i => hv i.succ))