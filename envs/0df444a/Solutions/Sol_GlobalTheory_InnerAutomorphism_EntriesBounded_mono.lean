-- Prove2me | solution 1 for GlobalTheory.InnerAutomorphism.EntriesBounded.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:54:12.686138+00:00
-- url     : https://prove2.me/submissions/4ef0166a-9f9d-4f7a-816b-1a479dc029e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SigmaSplitSymmInl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InnerAutomorphism
variable {K n : Type*} [NormedField K]
namespace GlobalTheory.InnerAutomorphism
namespace EntriesBounded
theorem _root_.solution {M : Matrix n n K} {c d : ℝ} (h : EntriesBounded M c)
    (hcd : c ≤ d) : EntriesBounded M d :=
  fun i j => (h i j).trans hcd
end EntriesBounded
end GlobalTheory.InnerAutomorphism
