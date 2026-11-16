-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.goodDm
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T08:16:19.490841+00:00
-- url     : https://prove2.me/submissions/78e1d1e7-6dcd-42c9-a4d4-1735926c58a5

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Lab
open AModelFac
open Matrix

variable {l p : Type*} [Fintype l] [Fintype p]

private theorem goodM_sub {N : ℕ} {A B : Matrix l p ℚ}
    (hA : GoodM N A) (hB : GoodM N B) : GoodM N (A - B) :=
  fun i j => (goodSub N).sub_mem (hA i j) (hB i j)

theorem solution {N o c : ℕ} (ho : GoodM N (Pc o)) (hc : GoodM N (Pc c)) :
    GoodM N (Dm o c) := by
  unfold Dm
  split_ifs
  · exact goodM_sub hc ho
  · exact goodM_sub ho hc
