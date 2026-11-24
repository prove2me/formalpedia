-- Prove2me | solution 1 for GlobalTheory.length_quotient_eq_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:22:34.709486+00:00
-- url     : https://prove2.me/submissions/cf245464-638a-47d9-84d7-87192269463a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Theorems.Thm_GlobalTheory_length_quotient_eq_finrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
namespace GlobalTheory
theorem _root_.solution (p : Ideal R) (n : Ideal S) [p.IsMaximal] [n.IsMaximal]
    [n.LiesOver p] [Module.Finite (R ⧸ p) (S ⧸ n)] :
    Module.length R (S ⧸ n) = (n.inertiaDeg R : ℕ∞) := by
  rw [length_quotient_eq_finrank R p n, Ideal.inertiaDeg_eq_of_isMaximal p n]
end GlobalTheory
