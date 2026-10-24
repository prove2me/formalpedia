-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.jet_selector_exists_repair7_b4ae670f_709b_4665_8d77_1253c6fa8d68
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:32:04.872029+00:00
-- url     : https://prove2.me/submissions/da4ef3b0-00ae-40a8-b747-4bc69caa1bc1

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Complex.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_jet_selector_exists_repair9_b4ae670f_709b_4665_8d77_1253c6fa8d68
open scoped BigOperators

theorem solution
    {n : Nat} {J : Type} [Fintype J] [DecidableEq J]
    (c : J → Fin n → Complex) (hc : Function.Injective c)
    (D : Nat) (j : J) (α : Fin n →₀ Nat) :
    ∃ E : MvPolynomial (Fin n) Complex,
      ∀ (k : J) (β : Fin n →₀ Nat),
        (∑ i : Fin n, β i) ≤ D →
        (MvPolynomial.aeval
          (fun i : Fin n => MvPolynomial.C (c k i) + MvPolynomial.X i) E).coeff β
          = if k = j ∧ β = α then 1 else 0 := by
  apply OAI.PiExponent.FormalInterpolation.jet_selector_exists_repair9_b4ae670f_709b_4665_8d77_1253c6fa8d68 <;> assumption
