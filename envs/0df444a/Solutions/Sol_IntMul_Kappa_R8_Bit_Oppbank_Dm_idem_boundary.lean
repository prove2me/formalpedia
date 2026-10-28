-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:36:01.647277+00:00
-- url     : https://prove2.me/submissions/d89dd126-42fe-4b62-bc27-e294a1da7b27

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNestBound
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.NestBound

/-- Boundary nestOK pairs: `Dm` is idempotent via NestBound (DimBound ⇒ dimCF ≤ 23). -/
theorem solution :
    ∀ o c, o < codeBound → c < codeBound →
      o ≤ 1 ∨ c ≤ 1 → Dm o c * Dm o c = Dm o c :=
  fun o c ho hc h => Dm_idem_boundary ho hc h
