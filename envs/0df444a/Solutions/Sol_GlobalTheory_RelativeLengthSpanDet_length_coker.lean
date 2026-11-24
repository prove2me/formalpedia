-- Prove2me | solution 1 for GlobalTheory.RelativeLengthSpanDet.length_coker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:32:43.91661+00:00
-- url     : https://prove2.me/submissions/2fdf4cc4-d3ef-4f00-90f2-755fcb16fa07

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanEqAddValDet
import Theorems.Thm_GlobalTheory_RelativeLengthSpanDet_length_coker_of_det_eq_zero
import Theorems.Thm_GlobalTheory_RelativeLengthSpanDet_length_coker_of_injective

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
theorem _root_.solution (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = addVal R P.det := by
  by_cases h : P.det = 0
  · rw [length_coker_of_det_eq_zero P h, h, addVal_zero]
  · have hinj : Function.Injective P.mulVecLin := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      by_contra hx0
      exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx0, hx⟩)
    rw [length_coker_of_injective (Pi.basisFun R ι) _ hinj, ← Matrix.toLin'_apply',
      LinearMap.det_toLin']
end GlobalTheory.RelativeLengthSpanDet
