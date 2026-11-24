-- Prove2me | solution 1 for GlobalTheory.LengthQuotientValuationDet.addVal_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:00.387926+00:00
-- url     : https://prove2.me/submissions/ffa69619-b257-4dd3-9614-7f6aba898471

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthQuotientSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthQuotientValuationDet
open Module IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace GlobalTheory.LengthQuotientValuationDet
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → R) :
    addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, AddValuation.map_mul, ih]
end GlobalTheory.LengthQuotientValuationDet
