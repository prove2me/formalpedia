-- Prove2me | solution 1 for GlobalTheory.topologicalKrullDim_eq_of_mem_irreducibleComponents_of_trdeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:01.432117+00:00
-- url     : https://prove2.me/submissions/63815f1c-a88c-428e-880a-8b955a31572f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_isEmbedding
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_forall_exists_isOpen
import Theorems.Thm_GlobalTheory_exists_affine_chart_trdeg_eq
import Theorems.Thm_GlobalTheory_mem_minimalPrimes_of_mem_irreducibleComponents
import Theorems.Thm_GlobalTheory_isClosed_image_of_mem_irreducibleComponents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory Topology Limits
variable {O : Type u} [CommRing O] [IsDomain O]
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of O)) [LocallyOfFiniteType f] [Flat f]
variable [IsDiscreteValuationRing O]
namespace GlobalTheory
theorem _root_.solution
    {S : Type*} [TopologicalSpace S]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {Z : Set S} (hZ : Z ∈ irreducibleComponents S) {d : ℕ}
    (hd : letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
      Algebra.trdeg O Y.functionField = d) :
    topologicalKrullDim Z = d := by
  have hirr : IsIrreducible (i '' Z) := hZ.1.image i hi.continuous.continuousOn
  have hη := hirr.isGenericPoint_genericPoint
    (isClosed_image_of_mem_irreducibleComponents f hi hr hZ)
  rw [← topologicalKrullDim_eq_of_isEmbedding (hi.comp (IsEmbedding.subtypeVal (p := (· ∈ Z))))
    (Z := i '' Z) (by rw [Set.range_comp, Subtype.range_coe])]
  refine topologicalKrullDim_eq_of_forall_exists_isOpen hirr.nonempty fun x hxZ ↦ ?_
  obtain ⟨A, _, _, _, _, _, j, _, hx, hj, hA⟩ := exists_affine_chart_trdeg_eq f x
  refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, ?_⟩
  obtain ⟨q, hq⟩ := (hη.specializes hxZ).mem_open j.isOpenEmbedding.isOpen_range hx
  rw [← hq] at hη
  have hmin := mem_minimalPrimes_of_mem_irreducibleComponents f hi hr hZ hj hη
  rw [← ringKrullDim_quotient_eq_of_mem_minimalPrimes O hmin (hA.trans hd),
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  refine topologicalKrullDim_eq_of_isEmbedding (j.isOpenEmbedding.isEmbedding.comp
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ (Ideal.Quotient.mk q.asIdeal)
      Ideal.Quotient.mk_surjective).isEmbedding) ?_
  refine (Set.range_comp _ _).trans
    (.trans (congrArg (Set.image j) ?_) Set.image_preimage_eq_range_inter)
  refine (range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).trans ?_
  rw [Ideal.mk_ker, ← hη.def, ← Set.image_singleton]
  exact (PrimeSpectrum.closure_singleton q).symm.trans
    (j.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image _)
end GlobalTheory
