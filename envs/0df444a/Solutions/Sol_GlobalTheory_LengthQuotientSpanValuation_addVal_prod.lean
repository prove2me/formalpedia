-- Prove2me | solution 1 for GlobalTheory.LengthQuotientSpanValuation.addVal_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:00.276973+00:00
-- url     : https://prove2.me/submissions/14e26d3d-25a6-40f1-b50e-ce4984d41fea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthSelfEqTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.LengthQuotientSpanValuation
open Module
variable {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace GlobalTheory.LengthQuotientSpanValuation
theorem _root_.solution {ι : Type*} (s : Finset ι) (a : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]
end GlobalTheory.LengthQuotientSpanValuation
