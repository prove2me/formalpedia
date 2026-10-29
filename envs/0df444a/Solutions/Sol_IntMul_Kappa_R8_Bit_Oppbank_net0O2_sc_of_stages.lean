-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_sc_of_stages
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:20:52.305242+00:00
-- url     : https://prove2.me/submissions/ae5c17e3-b989-4425-9d62-f272bcb05ead

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open IntMul.Kappa.R6.Bit (scalarStepH)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution
    (h12 : ∀ (vec : Fin 104719230 → ZMod 2) (w : Fin 104719230),
      ((List.range 1771).flatMap (blk2 (toNB ch0O))).foldl scalarStepH
        (((List.range 1771).flatMap (blk1 (toNB ch0O))).foldl scalarStepH
          (Sum.elim vec fun _ => 0)) (.inl (net0O.ρ w)) = vec w) :
    ∀ (vec : Fin 104719230 → ZMod 2) (w : Fin 104719230),
      net0O.prog.foldl scalarStepH (Sum.elim vec fun _ => 0) (.inl (net0O.ρ w)) = vec w := by
  intro vec w
  have h12' := h12 vec w
  -- Avoid clashing with geometry constant `v`.
  simp only [net0O, net, prog, show (v : ℕ) = 1771 from rfl] at h12' ⊢
  erw [List.foldl_append]
  exact h12'
