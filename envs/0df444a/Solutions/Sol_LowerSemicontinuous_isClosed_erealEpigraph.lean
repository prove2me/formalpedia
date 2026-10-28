-- Prove2me | solution 1 for LowerSemicontinuous.isClosed_erealEpigraph
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T00:31:19.012058+00:00
-- url     : https://prove2.me/submissions/44c1be15-4013-4685-86b6-8bb3ebe93926

import Mathlib

set_option autoImplicit false

-- carved verbatim out of submission 23d86335-ed0d-406b-b7dd-748579bde0b9, lines 194-200


theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hlsc : LowerSemicontinuous f) :
    IsClosed {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
  have h := hlsc.isClosed_epigraph
  exact h.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
