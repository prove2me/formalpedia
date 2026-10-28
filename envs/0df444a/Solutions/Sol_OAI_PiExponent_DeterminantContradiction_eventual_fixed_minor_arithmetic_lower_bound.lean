-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_arithmetic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:47:00.702529+00:00
-- url     : https://prove2.me/submissions/baf4d41e-924e-4e9b-a811-2ee34da67e04

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_fixed_minor_arithmetic_lower_bound_fixed_height_core

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (delta : Real) (hdelta : 0 < delta) :
    ∀ᶠ H : Real in atTop, 0 < H → 0 < actualRowCount d H →
      ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
          actualMean d H - 1 - d.arithmeticError - delta ≤
            Real.log ‖(actualMinor d H selection).det‖ /
              ((actualRowCount d H : Real) * H) := by
  filter_upwards [eventually_gt_atTop (0 : Real)] with H hH
  intro hHpos hrows selection hdet
  have hcore :=
    OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_arithmetic_lower_bound_fixed_height_core
      d H hHpos selection hdet
  have hbase : actualMean d H - 1 - d.arithmeticError ≤
      Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : Real) * H) := by
    linarith [hcore]
  linarith
