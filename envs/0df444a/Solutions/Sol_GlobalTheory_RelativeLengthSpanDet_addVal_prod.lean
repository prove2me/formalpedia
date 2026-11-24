-- Prove2me | solution 1 for GlobalTheory.RelativeLengthSpanDet.addVal_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:26.388628+00:00
-- url     : https://prove2.me/submissions/f89596d0-94a4-43f5-a946-1dd699b130ef

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanEqAddValDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RelativeLengthSpanDet
open IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]
namespace GlobalTheory.RelativeLengthSpanDet
theorem _root_.solution (s : Finset ι) (c : ι → R) :
    addVal R (∏ i ∈ s, c i) = ∑ i ∈ s, addVal R (c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]
end GlobalTheory.RelativeLengthSpanDet
