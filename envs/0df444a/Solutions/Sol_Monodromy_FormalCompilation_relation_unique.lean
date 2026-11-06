-- Prove2me | solution 1 for Monodromy.FormalCompilation.relation_unique
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:08:36.92907+00:00
-- url     : https://prove2.me/submissions/fea113d6-a55c-42d2-a835-5e3639d29118

import Definitions.Def_Monodromy_FormalCompilation

open Monodromy
open Monodromy.FormalCompilation
open Turing

variable (source : ToPartrec.Code)

theorem solution
    {configuration : TM2.Cfg (fun _ : Stack => Symbol) Label2 Store}
    {first second : TM1.Cfg Alphabet (Control1 source) Store}
    (first_related : TM2to1.TrCfg configuration first)
    (second_related : TM2to1.TrCfg configuration second) : first = second := by
  cases first_related with
  | mk firstTape first_stacks =>
    cases second_related with
    | mk secondTape second_stacks =>
      congr 2
      apply congrArg TM2to1.addBottom
      apply ListBlank.ext
      intro n
      funext k
      rw [TM2to1.stk_nth_val n (first_stacks k),
        TM2to1.stk_nth_val n (second_stacks k)]
