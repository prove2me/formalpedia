-- Prove2me | solution 1 for JRPHard.Periodic.reduction_to_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-15T20:02:28.668388+00:00
-- url     : https://prove2.me/submissions/5b6c3451-e673-4b27-9c0d-25b73b3f10d5

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting
open JRPHard.Periodic

theorem solution(M q₁ : ℕ) (hq₁ : 0 < q₁) :
    lemma2Cost M q₁ M = eoq2 M M + obj4 M q₁ := by
  unfold lemma2Cost periodicCost eoq2 obj4 JRPHard.Aperiodic.eoq coefK1 coefH1 coefK0
  push_cast
  ring
