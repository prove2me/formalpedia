-- Prove2me | solution 1 for GlobalTheory.inertiaDeg_eq_finrank_quotient_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:50.554684+00:00
-- url     : https://prove2.me/submissions/ba37c43f-b385-4dd4-a8da-dcad450da2b9

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
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
namespace GlobalTheory
theorem _root_.solution [Module.Finite R S] (n : Ideal S)
    [n.IsMaximal] :
    haveI := liesOver_maximalIdeal_of_isIntegral R S n
    n.inertiaDeg R = Module.finrank (R ⧸ maximalIdeal R) (S ⧸ n) :=
  haveI := liesOver_maximalIdeal_of_isIntegral R S n
  Ideal.inertiaDeg_eq_of_isMaximal _ _
end GlobalTheory
