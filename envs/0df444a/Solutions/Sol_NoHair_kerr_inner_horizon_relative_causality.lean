-- Prove2me | solution 1 for NoHair.kerr_inner_horizon_relative_causality
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:03:36.160824+00:00
-- url     : https://prove2.me/submissions/dbc14bc5-a636-4b28-a05f-00480a25ce67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_kerr_inner_horizon_chronology
import Theorems.Thm_NoHair_kerr_inner_horizon_global_hyperbolicity
import Theorems.Thm_NoHair_kerrNewman_outerHorizon_futureTrapped

open NoHair Set

theorem solution :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    ∃ T : VecField (kerrNewmanSpacetime 2), IsTimeOrientation g T ∧
      chronoPastSet g T A = A ∧ A ⊆ chronoFutureSet g T A ∧ IsGloballyHyperbolicOn g T A := by
  have hp : IsKerrNewmanBlackHoleParams (5/2) 2 0 := by norm_num [IsKerrNewmanBlackHoleParams]
  obtain ⟨hPast,hFuture⟩ := kerr_inner_horizon_chronology
  exact ⟨kerrNewmanTimeDirection (5/2) 2 0,(kerrNewman_outerHorizon_futureTrapped _ _ _ hp).1,
    hPast,hFuture,kerr_inner_horizon_global_hyperbolicity⟩
