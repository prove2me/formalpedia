-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:26:59.764736+00:00
-- url     : https://prove2.me/submissions/9df1d4c2-727b-45df-b004-5eecb9a9850a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
import Theorems.Thm_GlobalTheory_isIntegrallyClosed_quotient_of_mem_minimalPrimes
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F S : Type) [Field F] [CommRing S] [Algebra F S] [Algebra.Smooth F S] (q : Ideal S),
      q ∈ minimalPrimes S → IsIntegrallyClosed (S ⧸ q) := by
  intro F S _ _ _ _ q hq
  refine isIntegrallyClosed_quotient_of_mem_minimalPrimes (fun m _ => ?_) hq
  exact isDomain_and_isIntegrallyClosed_atPrime_of_smooth F m (Localization.AtPrime m)
end GlobalTheory
