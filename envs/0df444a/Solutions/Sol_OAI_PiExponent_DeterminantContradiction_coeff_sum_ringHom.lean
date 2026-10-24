-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.coeff_sum_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:07.704682+00:00
-- url     : https://prove2.me/submissions/0b6e037a-787f-46a0-ab4b-3ff5f97b9773

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib
open scoped BigOperators

open MeasureTheory Filter Topology in

theorem solution
    {α σ τ : Type*} [Fintype α] [DecidableEq σ] [DecidableEq τ]
    (φ : MvPolynomial σ Complex →+* MvPolynomial τ Complex)
    (e : τ →₀ Nat) (f : α → MvPolynomial σ Complex) :
    (φ (∑ x, f x)).coeff e = ∑ x, (φ (f x)).coeff e := by
  rw [map_sum, MvPolynomial.coeff_sum]
