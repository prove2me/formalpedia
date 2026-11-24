-- Prove2me | solution 1 for GlobalTheory.length_quotient_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:14:53.075312+00:00
-- url     : https://prove2.me/submissions/790d5d55-dc80-4d82-abf5-e42340ab75b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset

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
theorem _root_.solution (p : Ideal R) (n : Ideal S) [p.IsMaximal] [n.LiesOver p]
    [Module.Finite (R ⧸ p) (S ⧸ n)] :
    Module.length R (S ⧸ n) = (Module.finrank (R ⧸ p) (S ⧸ n) : ℕ∞) := by
  letI := Ideal.Quotient.field p
  rw [Module.length_eq_of_surjective (S := R) (R := R ⧸ p) Ideal.Quotient.mk_surjective,
    Module.length_eq_finrank]
end GlobalTheory
