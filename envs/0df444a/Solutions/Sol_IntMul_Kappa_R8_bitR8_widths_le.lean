-- Prove2me | solution 1 for IntMul.Kappa.R8.bitR8_widths_le
-- status  : ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:19:14.373616+00:00
-- url     : https://prove2.me/submissions/40ca2fc1-1c8a-4658-9de1-2183fb1c3634

import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa.Jain

/-- Every child width in the round-eight bit histogram is at most $m = 529$. -/
theorem solution : ∀ p ∈ bitR8, p.1 ≤ 529 := by
  decide
