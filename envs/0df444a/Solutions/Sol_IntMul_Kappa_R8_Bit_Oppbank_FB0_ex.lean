-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.FB0_ex
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:05:23.864399+00:00
-- url     : https://prove2.me/submissions/0b054b3e-9bfc-425a-96aa-2d0c4101e590
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.


import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Theorems.Thm_IntMul_Kappa_R6_Bit_NB_flagBasis
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_hPis0
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped Kronecker
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.NetFB
open IntMul.Kappa.R8.Bit.Oppbank

/-! Full FB0_ex via flagBasis Lab0 hLab0 Pis0 hPis0.
NetFB.hLab0 is on ProjB.Lab0; Pnd.Lab0 is definitionally the same shape. -/

theorem solution : ∃ S Sinv, FB0 S Sinv := by
  have hLab : ∀ p ∈ Lab0, p.2 ⬝ᵥ p.1 = 1 := by
    intro p hp
    unfold Lab0 at hp
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hp
    exact yx (Finset.mem_range.1 hT)
  exact flagBasis Lab0 hLab Pis0 hPis0
