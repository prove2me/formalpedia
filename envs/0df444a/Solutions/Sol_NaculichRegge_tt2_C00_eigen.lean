-- Prove2me | solution 1 for NaculichRegge.tt2_C00_eigen
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T21:52:34.61459+00:00
-- url     : https://prove2.me/submissions/16b7c969-b432-4395-badb-e3f828c67c2a

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial
open NaculichRegge

theorem solution : Tt2.mulVec C00 = (X : ℂ[X]) • C00 := by
  ext i
  fin_cases i <;> simp [Tt2, C00, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
