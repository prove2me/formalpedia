-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.hPis0_Dm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:30:06.812257+00:00
-- url     : https://prove2.me/submissions/f06640b8-2b16-4b5e-bc12-ec6787de7929
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_interior
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_Dm_idem_boundary
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false

open Matrix Finset
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3
open IntMul.Kappa.R8.Bit.Oppbank

theorem solution : ∀ A ∈ idxD.image (fun p => Dm p.1 p.2), A * A = A := by
  intro A hA
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hA
  -- use MoveFacts3.mem_idxD (does not unfold irreducible idxD globally)
  have hp' := (MoveFacts3.mem_idxD p).1 hp
  have ho : p.1 < codeBound := hp'.1.1
  have hc : p.2 < codeBound := hp'.1.2
  have hnest : nestOK p.1 p.2 = true := hp'.2
  have hoS : p.1 < SupG.codeBound := by simpa [SupG.codeBound, codeBound] using ho
  have hcS : p.2 < SupG.codeBound := by simpa [SupG.codeBound, codeBound] using hc
  by_cases hbd : p.1 ≤ 1 ∨ p.2 ≤ 1
  · exact Dm_idem_boundary p.1 p.2 hoS hcS hbd
  · have hbd' : ¬ p.1 ≤ 1 ∧ ¬ p.2 ≤ 1 := by
      exact not_or.1 hbd
    exact Dm_idem_interior p.1 p.2 hoS hcS hnest hbd'.1 hbd'.2
