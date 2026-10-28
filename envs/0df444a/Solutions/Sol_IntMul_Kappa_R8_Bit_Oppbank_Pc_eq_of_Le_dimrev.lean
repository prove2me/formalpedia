-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Pc_eq_of_Le_dimrev
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:12:55.344157+00:00
-- url     : https://prove2.me/submissions/393d2b69-d720-47b7-8cee-af6989badd52
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Pc_rank
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_le_eq_of_rank
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3
open IntMul.Kappa.R8.Bit.Oppbank.SupG

theorem solution {a b : ℕ} (ha : a < codeBound) (hb : b < codeBound)
    (hLe : Le (Pc a) (Pc b)) (hdim : dimCF b ≤ dimCF a) :
    Pc a = Pc b := by
  have hia := Pc_idem ha
  have hib := Pc_idem hb
  -- le_eq_of_rank needs rank B ≤ rank A, here B=Pc a, A=Pc b? 
  -- Le A B means Le (Pc a)(Pc b): B=Pc b, A=Pc a in le_eq naming: Le A B with A=Pc a, B=Pc b
  -- le_eq_of_rank hA hB h hr : B = A when Le A B and B.rank ≤ A.rank
  -- So we need (Pc b).rank ≤ (Pc a).rank, i.e. dimCF b ≤ dimCF a via Pc_rank
  have hr : (Pc b).rank ≤ (Pc a).rank := by
    rw [Pc_rank ha, Pc_rank hb]; exact hdim
  exact (le_eq_of_rank hia hib hLe hr).symm
