-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_LabFinal_of_stages
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:58:06.750827+00:00
-- url     : https://prove2.me/submissions/4546c432-bee3-4f43-986e-c358e83d94c6

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open AModel (swapMat)
open IntMul.Kappa.R6.Bit (labStepH)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution (N : ℕ) (_h : EOKO ch0NB N)
    (h2 : ∀ w, ((List.range 1771).flatMap (blk2 (toNB ch0O))).foldl (labStepH N)
      (((List.range 1771).flatMap (blk1 (toNB ch0O))).foldl (labStepH N) (fun _ => 1))
      (.inl (net0O.ρ w)) = swapMat) :
    ∀ w, net0O.prog.foldl (labStepH N) (fun _ => 1) (.inl (net0O.ρ w)) = swapMat := by
  intro w
  have h2' := h2 w
  -- Unfold to stage lists; use `erw` so NI abbrev matches Instr.
  simp only [net0O, net, prog, v] at h2' ⊢
  erw [List.foldl_append]
  exact h2'
