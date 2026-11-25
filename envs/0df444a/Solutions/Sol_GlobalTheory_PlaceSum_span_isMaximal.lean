-- Prove2me | solution 1 for GlobalTheory.PlaceSum.span_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:30:24.22206+00:00
-- url     : https://prove2.me/submissions/6cac3f29-bf4f-4bd5-bcc4-f0ae17b09e22

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumFinitePlacesLeSumOverPrimes
import Theorems.Thm_GlobalTheory_PlaceSum_span_ne_bot

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
    (Nat.prime_iff_prime_int.mp hp)).isMaximal (span_ne_bot hp)
end GlobalTheory.PlaceSum
