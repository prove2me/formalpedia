-- Prove2me | solution 1 for Kyprianou.ProofPreparation.real_two_var_weighted_square_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:37:24.193521+00:00
-- url     : https://prove2.me/submissions/bcbdea80-1623-4ff7-9e47-fd15ff463477

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

/-- Expand and integrate the square of two weighted real functions. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → ℝ)
    (hXX : Integrable (fun ω => X ω ^ 2) P)
    (hYY : Integrable (fun ω => Y ω ^ 2) P)
    (hXY : Integrable (fun ω => X ω * Y ω) P)
    (a b : ℝ) :
    (∫ ω, (a * X ω + b * Y ω) ^ 2 ∂P) =
      a ^ 2 * (∫ ω, X ω ^ 2 ∂P) +
      b ^ 2 * (∫ ω, Y ω ^ 2 ∂P) +
      (2 * a * b) * (∫ ω, X ω * Y ω ∂P) := by
  have h1 := hXX.const_mul (a ^ 2)
  have h2 := hYY.const_mul (b ^ 2)
  have h3 := hXY.const_mul (2 * a * b)
  calc
    (∫ ω, (a * X ω + b * Y ω) ^ 2 ∂P) =
        (∫ ω, (a ^ 2 * X ω ^ 2 + b ^ 2 * Y ω ^ 2) +
          (2 * a * b) * (X ω * Y ω) ∂P) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by ring
    _ = ((∫ ω, a ^ 2 * X ω ^ 2 ∂P) +
        (∫ ω, b ^ 2 * Y ω ^ 2 ∂P)) +
        (∫ ω, (2 * a * b) * (X ω * Y ω) ∂P) := by
      calc
        (∫ ω, (a ^ 2 * X ω ^ 2 + b ^ 2 * Y ω ^ 2) +
          (2 * a * b) * (X ω * Y ω) ∂P) =
            (∫ ω, a ^ 2 * X ω ^ 2 + b ^ 2 * Y ω ^ 2 ∂P) +
            (∫ ω, (2 * a * b) * (X ω * Y ω) ∂P) :=
          integral_add (h1.add h2) h3
        _ = _ := by rw [integral_add h1 h2]
    _ = _ := by
      simp only [integral_const_mul]
