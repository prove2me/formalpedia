-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.nestOK_of_rkC_pos
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T07:17:27.723494+00:00
-- url     : https://prove2.me/submissions/da0652c9-ea90-4fbc-b14e-9a7c3c0ee167

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The target is elaborated inside namespace `IntMul.Kappa.R8.Bit.Oppbank`; the empty block registers it for `open`.
namespace IntMul.Kappa.R8.Bit.Oppbank
end IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul IntMul.Kappa IntMul.Kappa.R8 IntMul.Kappa.R8.Bit IntMul.Kappa.R8.Bit.Oppbank in
theorem solution :
    ¬ (∀ {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound) (hr : 0 < rkC o c), nestOK o c = true) := by
  intro claimed
  have h := claimed (o := 1773) (c := 3544) (by decide) (by decide) (by decide)
  revert h
  decide

#print axioms solution
