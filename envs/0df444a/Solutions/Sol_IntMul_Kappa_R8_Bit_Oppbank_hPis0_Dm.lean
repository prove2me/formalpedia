-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.hPis0_Dm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:34:46.353829+00:00
-- url     : https://prove2.me/submissions/ad647046-0631-44aa-a4fb-1c73d7b6659a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_boundary
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_interior
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution : ∀ A ∈ idxD.image (fun p => Dm p.1 p.2), A * A = A := by
  intro A hA
  obtain ⟨⟨o, c⟩, hp, rfl⟩ := Finset.mem_image.1 hA
  have hp' := (mem_idxD _).1 hp
  have ho : o < SupG.codeBound := by simpa [SupG.codeBound] using hp'.1.1
  have hc : c < SupG.codeBound := by simpa [SupG.codeBound] using hp'.1.2
  by_cases hble : o ≤ 1 ∨ c ≤ 1
  · exact Dm_idem_boundary o c ho hc hble
  · push_neg at hble
    exact Dm_idem_interior o c ho hc hp'.2 (not_le.mpr hble.1) (not_le.mpr hble.2)
