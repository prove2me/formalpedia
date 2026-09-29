-- Prove2me | solution 1 for Leopoldt.units_rank_of_isTotallyReal
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:43:14.942926+00:00
-- url     : https://prove2.me/submissions/017ffd4f-3e22-45bf-b11c-50d2bee4410d

import Definitions.Def_LeopoldtDefect

open NumberField IsDedekindDomain Leopoldt

theorem solution (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] :
    Units.rank K = Module.finrank ℚ K - 1 := by
  rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
    add_zero, IsTotallyReal.finrank]
