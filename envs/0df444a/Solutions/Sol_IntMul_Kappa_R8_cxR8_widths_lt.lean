-- Prove2me | solution 1 for IntMul.Kappa.R8.cxR8_widths_lt
-- status  : ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:19:14.878978+00:00
-- url     : https://prove2.me/submissions/e6e9359d-d6ce-403b-975b-034d93054046

import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.Jain

/-- Every child width in the round-eight complex histogram is strictly less than $m = 576$. -/
theorem solution : ∀ p ∈ cxR8, p.1 < 576 := by
  decide
