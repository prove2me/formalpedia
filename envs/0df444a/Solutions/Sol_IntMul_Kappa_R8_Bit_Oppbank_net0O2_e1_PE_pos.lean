-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_e1_PE_pos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:11:02.865996+00:00
-- url     : https://prove2.me/submissions/4dc4ace7-88f5-4266-baa4-5ccf88a90b44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunPE2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e1_K_idem
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e1_K_rank
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e1_K_pivs
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_rkC_lt_529
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunPE2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem solution (b o c : ℕ) (hb : b < v) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    ∃ e, OneRunNet2.PE (K S0 Si0 (Dm o c) (Pl b)) (oneRun (rkC o c)) e := by
  refine oneRun_of_pivs (rkC o c) hr (rkC_lt_529 o c)
    (K S0 Si0 (Dm o c) (Pl b)) ?hidem (net0O2_e1_K_rank b o c hb ho hc hr)
    (net0O2_e1_K_pivs b o c hb ho hc hr)
  -- net0O2_e1_K_idem concludes `let q := K ...; q*q=q`
  simpa using net0O2_e1_K_idem b o c hb ho hc hr
