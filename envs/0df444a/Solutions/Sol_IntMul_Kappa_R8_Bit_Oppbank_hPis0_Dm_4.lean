-- Prove2me | solution 4 for IntMul.Kappa.R8.Bit.Oppbank.hPis0_Dm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:38:07.038966+00:00
-- url     : https://prove2.me/submissions/f63bcc3b-b8bf-4eda-8431-f66b507cfdd4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_boundary
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_interior
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution :
    ∀ A ∈ idxD.image (fun p => Dm p.1 p.2), A * A = A := by
  intro A hA
  obtain ⟨⟨o, c⟩, hp, rfl⟩ := Finset.mem_image.1 hA
  have hp' := (mem_idxD _).1 hp
  have ho : o < codeBound := hp'.1.1
  have hc : c < codeBound := hp'.1.2
  have hn : nestOK o c = true := hp'.2
  by_cases hble : o ≤ 1 ∨ c ≤ 1
  · exact Dm_idem_boundary o c ho hc hble
  · exact Dm_idem_interior o c ho hc hn
      (fun h => hble (Or.inl h)) (fun h => hble (Or.inr h))
