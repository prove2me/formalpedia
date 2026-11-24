-- Prove2me | solution 1 for GlobalTheory.SignedLengthTower.ord_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:07.426324+00:00
-- url     : https://prove2.me/submissions/b1d649ad-6c93-478e-8a5e-eed0c98567df

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthTower
namespace GlobalTheory.SignedLengthTower
theorem _root_.solution {R ι : Type*} [CommRing R] [IsDomain R] (s : Finset ι) (d : ι → R)
    (hd : ∀ i, d i ≠ 0) : Ring.ord R (∏ i ∈ s, d i) = ∑ i ∈ s, Ring.ord R (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ring.ord_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hd i)), ih]
end GlobalTheory.SignedLengthTower
