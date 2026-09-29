-- Prove2me | solution 1 for IsLocalRing.quotient_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/18bba953-a074-5378-855d-bc1795040c3c

import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_quotient_of_ne_top

open IsLocalRing

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤) :
    IsLocalRing (A ⧸ I) :=
  haveI := Ideal.Quotient.nontrivial_iff.mpr hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

end S_IsLocalRing_quotient_of_ne_top
end P2MW
export P2MW.S_IsLocalRing_quotient_of_ne_top (solution)
