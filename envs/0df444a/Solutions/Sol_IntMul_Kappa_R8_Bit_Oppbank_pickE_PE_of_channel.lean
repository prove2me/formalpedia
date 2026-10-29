-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.pickE_PE_of_channel
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:05:02.355383+00:00
-- url     : https://prove2.me/submissions/a17fbb13-fce4-42ea-a59a-fb4654e52818

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank IntMul.Kappa.R6.Bit IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2 Matrix in
theorem solution (q : Matrix (Fin 529) (Fin 529) ℚ) (r : ℕ)
    (e : Edge 529) (he : e = pickE (PE q (oneRun r))) (hne : e ≠ dfltE) :
    (∃ e', PE q (oneRun r) e') ∧ e = pickE (PE q (oneRun r)) := by
  refine ⟨?_, he⟩
  by_contra h
  apply hne
  rw [he]
  unfold IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2.pickE
  rw [dif_neg h]
