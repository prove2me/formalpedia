-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncatedPolynomialPacket_row_exponent_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:19:16.926626+00:00
-- url     : https://prove2.me/submissions/b576a0aa-6aac-4073-a1f8-393d88687e5b

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation
theorem solution
    {m : Nat} (K : Nat) (v0 theta : Real) (w : Fin m → Real)
    (R : Real) (e : Fin (m + 1) → Nat) (n : Nat)
    (rho : InterpolationMatrix.Row K v0 theta w ((n : Real) * R))
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : Real) * InterpolationMatrix.rowWeights v0 theta w i) :
    ∀ i, rho.2.1 i < n * e i := by
  intro i
  have hmem := rho.2.2
  simp only [OAI.PiExponent.strictWeightedSimplex, Finset.mem_filter] at hmem
  have hlt := hmem.2
  set rw := InterpolationMatrix.rowWeights v0 theta w
  set a := rho.2.1
  have hpos : ∀ j, 0 < rw j := fun j => by
    have h1 := hscale j
    have h2 : (0 : ℝ) < e j := by exact_mod_cast he j
    by_contra hc
    push Not at hc
    nlinarith
  have hsingle : rw i * (a i : ℝ) ≤ ∑ j, rw j * (a j : ℝ) :=
    Finset.single_le_sum (f := fun j => rw j * (a j : ℝ))
      (fun j _ => mul_nonneg (hpos j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
  have key : rw i * (a i : ℝ) < rw i * ((n : ℝ) * e i) := by
    have := hscale i
    nlinarith
  have := lt_of_mul_lt_mul_left key (hpos i).le
  exact_mod_cast this
