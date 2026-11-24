-- Prove2me | solution 1 for GlobalTheory.RelativeLengthSpanDet.relLength_span_eq_addVal_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:46:59.355393+00:00
-- url     : https://prove2.me/submissions/8f65d28a-6758-4d87-a7a3-367a432352dc

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanEqAddValDet
import Theorems.Thm_GlobalTheory_RelativeLengthSpanDet_length_coker

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module R V] {a v : ι → V}
    (ha : LinearIndependent R a) (P : Matrix ι ι R) (hv : ∀ j, v j = ∑ i, P i j • a i) :
    relLength (Submodule.span R (Set.range a)) (Submodule.span R (Set.range v)) =
      addVal R P.det := by
  have hinj : Function.Injective (Fintype.linearCombination R a) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    exact Fintype.linearIndependent_iff.mp ha x (by rwa [Fintype.linearCombination_apply] at hx) i
  have hA : Submodule.span R (Set.range a) =
      (⊤ : Submodule R (ι → R)).map (Fintype.linearCombination R a) := by
    rw [Submodule.map_top, Fintype.range_linearCombination]
  have hcomp : Fintype.linearCombination R a ∘ₗ P.mulVecLin = Fintype.linearCombination R v := by
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    simp [Fintype.linearCombination_apply, hv, Pi.single_apply]
  have hB : Submodule.span R (Set.range v) =
      (LinearMap.range P.mulVecLin).map (Fintype.linearCombination R a) := by
    rw [← LinearMap.range_comp, hcomp, Fintype.range_linearCombination]
  rw [hA, hB, relLength_map_of_injective _ hinj, relLength_top_left, length_coker]
end GlobalTheory.RelativeLengthSpanDet
