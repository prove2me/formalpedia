-- Prove2me | solution 1 for NetworkEquilibriumCLS.LinearNash.clsHard_trans
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:45:09.954796+00:00
-- url     : https://prove2.me/submissions/a0c8ebef-57f9-4c03-add9-d9fbff90bdc5

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Theorems.Thm_ConstrSOSP_searchReduces_trans

open NetworkEquilibriumCLS.LinearNash


theorem solution {Q R : SearchProblem}
    (hQ : CLSHard Q) (hQR : SearchReduces Q R) : CLSHard R := by
  intro S hS
  exact ConstrSOSP.searchReduces_trans S Q R (hQ S hS) hQR
