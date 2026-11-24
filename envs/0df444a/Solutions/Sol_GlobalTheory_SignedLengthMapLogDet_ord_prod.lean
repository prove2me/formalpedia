-- Prove2me | solution 1 for GlobalTheory.SignedLengthMapLogDet.ord_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:05.059712+00:00
-- url     : https://prove2.me/submissions/a788a542-fd1a-4d76-921f-c1d56a840a7c

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.SignedLengthMapLogDet
open Module
variable {R : Type*} [CommRing R] [IsDomain R]
namespace GlobalTheory.SignedLengthMapLogDet
theorem _root_.solution {ι : Type*} (s : Finset ι) (a : ι → R) (ha : ∀ i, a i ≠ 0) :
    Ring.ord R (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (ha i)), ih]
end GlobalTheory.SignedLengthMapLogDet
