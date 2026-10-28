-- Prove2me | solution 1 for IntMul.Kappa.R8.cxR8_widths
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:06:07.725125+00:00
-- url     : https://prove2.me/submissions/734da620-9ddf-408e-af99-adc3a2a69b1a

import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.Jain

/-- Concrete list inspection of `Jain.cxR8`. -/
theorem solution : ∀ p ∈ cxR8, 0 < p.1 ∧ p.1 ≤ 529 := by
  decide
