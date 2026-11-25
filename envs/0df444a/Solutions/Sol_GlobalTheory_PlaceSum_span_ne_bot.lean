-- Prove2me | solution 1 for GlobalTheory.PlaceSum.span_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:21:51.538032+00:00
-- url     : https://prove2.me/submissions/842d7919-6c1a-466c-bec5-373b43e91693

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumFinitePlacesLeSumOverPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
open GlobalTheory GlobalTheory.PlaceSum
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.PlaceSum
theorem _root_.solution {p : ℕ} (hp : p.Prime) : Ideal.span {(p : ℤ)} ≠ ⊥ := by
  simpa using hp.ne_zero
end GlobalTheory.PlaceSum
