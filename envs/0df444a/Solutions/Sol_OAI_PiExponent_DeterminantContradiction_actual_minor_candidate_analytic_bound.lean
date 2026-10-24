-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_minor_candidate_analytic_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:32:22.978441+00:00
-- url     : https://prove2.me/submissions/d47fd628-1383-48e4-b08c-c3baf8b2f8ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_log_bound_by_translation_expansion
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_count_log_bound

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution {nu : Real} (d : FixedData nu) {H : Real}
    (hH : 0 < H) (selection : Row d H → Column d H)
    (hne : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : Real) * H) ≤
      d.analyticError +
        (Real.log (actualRowCount d H : Real) + Real.log 2 / 4 -
          Real.log (1 - Real.exp (-Real.log 2 / 2)) +
          Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1))) / H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)) := by
  have hnu : 0 ≤ nu := by
    have hthetaone : (d.base.theta : Real) < 1 :=
      lt_trans d.base.theta_lt_A (lt_trans d.base.A_lt_B d.base.B_lt_one)
    have hcoeff : 0 < (d.base.A : Real) - d.base.theta := by
      exact sub_pos.mpr d.base.theta_lt_A
    have hprod : 0 < nu * ((d.base.A : Real) - d.base.theta) :=
      lt_trans (sub_pos.mpr hthetaone) d.base.approximation_gap
    by_contra hn
    have hnonpos : nu ≤ 0 := le_of_lt (not_le.mp hn)
    have hmul := mul_nonpos_of_nonpos_of_nonneg hnonpos hcoeff.le
    linarith
  have hraw :=
    OAI.PiExponent.DeterminantContradiction.actual_minor_log_bound_by_translation_expansion
      d hnu hH selection hne
  have hcount :=
    OAI.PiExponent.DeterminantContradiction.translation_count_log_bound d hH
  calc
    _ ≤ d.analyticError +
        (Real.log (actualRowCount d H : Real) + Real.log 2 / 4 -
          Real.log (1 - Real.exp (-Real.log 2 / 2))) / H +
        Real.log
          ((((⌊H⌋₊ + 1) ^ (2 * d.m) *
            (⌊H / (d.v0 : Real)⌋₊ + 1) : Nat) : Real)) / H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)) := hraw
    _ ≤ d.analyticError +
        (Real.log (actualRowCount d H : Real) + Real.log 2 / 4 -
          Real.log (1 - Real.exp (-Real.log 2 / 2))) / H +
        Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1)) / H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)) := by
      have hratio := div_le_div_of_nonneg_right hcount hH.le
      linarith
    _ = d.analyticError +
        (Real.log (actualRowCount d H : Real) + Real.log 2 / 4 -
          Real.log (1 - Real.exp (-Real.log 2 / 2)) +
          Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1))) / H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)) := by
      ring