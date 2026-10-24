-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_analytic_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:05:35.620352+00:00
-- url     : https://prove2.me/submissions/4978c2a6-5087-4958-ab44-ef9a780d4d1d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_fixed_minor_analytic_upper_bound_analyticAggregate

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (delta : Real) (hdelta : 0 < delta) :
    ∀ᶠ H : Real in atTop, 0 < H → 0 < actualRowCount d H →
      ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
          Real.log ‖(actualMinor d H selection).det‖ /
              ((actualRowCount d H : Real) * H) ≤
            d.analyticError + delta +
              max (-collisionRate d H)
                (-nu * ((d.base.A : Real) * (1 - d.base.eta) -
                  actualMean d H)) := by
  have haggregate :=
    OAI.PiExponent.DeterminantContradiction.eventual_fixed_minor_analytic_upper_bound_analyticAggregate
      nu d
  obtain ⟨error, herror, hbound⟩ := haggregate
  have heventually :
      ∀ᶠ H : Real in atTop, error H ≤ delta := by
    have hsmall : ∀ᶠ H : Real in atTop, |error H| < delta := by
      have hdist := (Metric.tendsto_nhds.1 herror) delta hdelta
      simpa [Real.dist_eq] using hdist
    filter_upwards [hsmall] with H hH
    exact le_trans (le_abs_self _) (le_of_lt hH)
  filter_upwards [heventually, hbound] with H herr hminor Hpos hcount selection hdet
  have hdenom : 0 < (actualRowCount d H : Real) * H :=
    mul_pos (Nat.cast_pos.mpr hcount) Hpos
  apply (div_le_iff₀ hdenom).2
  have hmul := (div_le_iff₀ hdenom).mp (hminor selection hdet)
  calc
    Real.log ‖(actualMinor d H selection).det‖ ≤
        (d.analyticError + error H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : Real) * (1 - d.base.eta) -
              actualMean d H))) *
          ((actualRowCount d H : Real) * H) := hmul
    _ ≤ (d.analyticError + delta +
          max (-collisionRate d H)
            (-nu * ((d.base.A : Real) * (1 - d.base.eta) -
              actualMean d H))) *
          ((actualRowCount d H : Real) * H) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hdenom)
      linarith
