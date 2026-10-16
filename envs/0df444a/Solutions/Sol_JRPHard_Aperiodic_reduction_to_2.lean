-- Prove2me | solution 1 for JRPHard.Aperiodic.reduction_to_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-15T20:02:39.727303+00:00
-- url     : https://prove2.me/submissions/93c02175-610e-48fe-b3b0-ee4758459be7

import Mathlib
import Definitions.Def_JRPHard_Aperiodic_Setting
open JRPHard.Aperiodic

theorem solution(M : ℕ) (hodd : Odd M) (h1 : 1 < M) (hcomp : ¬ M.Prime)
    (q : ℕ) (hq : 0 < q) :
    lemma1Cost M q M = eoq2 M M + jrpRed M q := by
  have hM1 : 1 ≤ M := by omega
  unfold lemma1Cost aperiodicCost eoq2 jrpRed eoq coefK0 coefK1 coefH1
  push_cast [Nat.cast_sub hM1]
  ring
