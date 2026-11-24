-- Prove2me | solution 1 for GlobalTheory.SignedLengthLogDet.ord_finprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:48:14.287797+00:00
-- url     : https://prove2.me/submissions/9c4826fd-d3a6-4240-ac40-36ae1661597c

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthEqLogOrdFracDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthLogDet
open Module
namespace GlobalTheory.SignedLengthLogDet
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} (s : Finset ι)
    (c : ι → R) (hc : ∀ i, c i ≠ 0) :
    Ring.ord R (∏ i ∈ s, c i) = ∑ i ∈ s, Ring.ord R (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hc i)), ih]
end GlobalTheory.SignedLengthLogDet
