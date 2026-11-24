-- Prove2me | solution 1 for GlobalTheory.LengthCokernelInjective.addVal_finset_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:16.931937+00:00
-- url     : https://prove2.me/submissions/8863220b-a715-491c-994b-d486ed453fca

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCokerOfNotInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthCokernelInjective
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace GlobalTheory.LengthCokernelInjective
theorem _root_.solution {ι : Type*} (s : Finset ι) (a : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]
end GlobalTheory.LengthCokernelInjective
