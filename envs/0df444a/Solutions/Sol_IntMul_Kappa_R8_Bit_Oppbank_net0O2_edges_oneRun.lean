-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_edges_oneRun
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:54:56.00784+00:00
-- url     : https://prove2.me/submissions/6b931ac0-8e9c-437e-a158-4cf6e0c8b51f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_edges_as_pickE
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_pickE_oneRun
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank
open Matrix

theorem solution :
    ∀ e ∈ net0O.edges, ∃ r, oneRun r e.runs := by
  intro e he
  obtain ⟨r, q, hPE, heq⟩ := net0O2_edges_as_pickE e he
  refine ⟨r, ?_⟩
  have h := net0O2_pickE_oneRun r q hPE
  simpa [heq] using h
