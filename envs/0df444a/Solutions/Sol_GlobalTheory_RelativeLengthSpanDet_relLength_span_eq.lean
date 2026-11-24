-- Prove2me | solution 1 for GlobalTheory.RelativeLengthSpanDet.relLength_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:59:55.595465+00:00
-- url     : https://prove2.me/submissions/d9758afc-7418-4162-8a15-1f66da55fb40

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanEqAddValDet
import Theorems.Thm_GlobalTheory_RelativeLengthSpanDet_relLength_span_eq_addVal_det

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
namespace GlobalTheory.RelativeLengthSpanDet
universe u_1 u_2 u_3 in
theorem _root_.solution {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {V : Type u_2} [AddCommGroup V] [Module R V] {ι : Type u_3} [Fintype ι] [DecidableEq ι]
    {a v : ι → V} (ha : LinearIndependent R a) (P : Matrix ι ι R)
    (hv : ∀ j, v j = ∑ i, P i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range v)) =
      (addVal R : R → ℕ∞) P.det :=
  relLength_span_eq_addVal_det ha P hv
end GlobalTheory.RelativeLengthSpanDet
