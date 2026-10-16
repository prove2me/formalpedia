-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.hasWeightedSupport_fin_prod_series
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T06:14:40.479162+00:00
-- url     : https://prove2.me/submissions/fdcf11ac-52f3-4c3d-8ae9-88f316c80ba2

import Definitions.Def_OAI_PiExponent_WeightedSupport
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_finset_prod_series

open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution {m : ℕ} (v : Fin (m + 1) → ℝ) (R : ℝ) (n : ℕ)
    (s : Fin n → MvPowerSeries (Fin (m + 1)) ℂ)
    (hs : ∀ i, hasWeightedSupport v R (s i)) :
    hasWeightedSupport v ((n : ℝ) * R) (∏ i, s i) := by
  have h :=
    OAI.PiExponent.FormalInterpolation.hasWeightedSupport_finset_prod_series
      (v := v) (R := R) (t := (Finset.univ : Finset (Fin n))) (f := s)
      (by
        intro i hi
        exact hs i)
  simpa using h
