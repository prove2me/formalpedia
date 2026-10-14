-- Prove2me | solution 1 for MDOUnifiedCosmology.deceleration_formula
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:13:41.48416+00:00
-- url     : https://prove2.me/submissions/2debea04-b7a2-4147-8edc-aec1c28cda76

import Definitions.Def_MDOUnifiedCosmology_model
open MDOUnifiedCosmology Set

theorem solution (a : ℝ → ℝ) (t : ℝ) (ha : DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t) (ha0 : a t ≠ 0) (had : deriv a t ≠ 0) :
    decelerationParam a t = -1 - deriv (hubble a) t / hubble a t ^ 2 := by
  have hh : deriv (hubble a) t = (deriv (deriv a) t * a t - deriv a t * deriv a t) / (a t)^2 :=
    (ha'.hasDerivAt.div ha.hasDerivAt ha0).deriv
  unfold decelerationParam
  rw [hh]
  unfold hubble
  field_simp
  ring


