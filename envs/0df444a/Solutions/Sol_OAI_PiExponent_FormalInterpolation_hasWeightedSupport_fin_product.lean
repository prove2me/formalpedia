-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_fin_product
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:10:08.236179+00:00
-- url     : https://prove2.me/submissions/e4b47ad9-08eb-44a0-b01c-f82402ae98da

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_fin_prod_series

open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution {m : ℕ} (v : Fin (m + 1) → ℝ) (R : ℝ) (n : ℕ)
    (f : MvPolynomial (Fin (m + 1)) ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (hf0 : ∀ Q, hasWeightedSupport v 0 (f Q))
    (hI : ∀ Q, Q ∈ I → hasWeightedSupport v R (f Q))
    (s : Fin n → MvPolynomial (Fin (m + 1)) ℂ)
    (hs : ∀ i, s i ∈ I) :
    hasWeightedSupport v ((n : ℝ) * R) (f (∏ i, s i)) := by
  simpa only [map_prod] using
    OAI.PiExponent.FormalInterpolation.hasWeightedSupport_fin_prod_series
      v R n (fun i => f (s i)) (by
        intro i
        exact hI (s i) (hs i))