-- Prove2me | solution 1 for GlobalTheory.ringKrullDim_stalk_eq_one_of_mem_irreducibleComponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:46.335801+00:00
-- url     : https://prove2.me/submissions/64a59117-3497-4802-ae03-a19dc5fad11a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
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
    {Z : Set S} (hZ : Z ∈ irreducibleComponents S) {z : S} (hz : IsGenericPoint z Z) :
    ringKrullDim (Y.presheaf.stalk (i z)) = 1 := by
  have hη : IsGenericPoint (i z) (i '' Z) := by
    have := hz.image hi.continuous
    rwa [(isClosed_image_of_mem_irreducibleComponents f hi hr hZ).closure_eq] at this
  obtain ⟨A, _, _, _, _, _, j, _, ⟨q, hq⟩, hj, -⟩ := exists_affine_chart_trdeg_eq f (i z)
  rw [← hq] at hη ⊢
  have hmin := mem_minimalPrimes_of_mem_irreducibleComponents f hi hr hZ hj hη
  rw [ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap q)).commRingCatIsoToRingEquiv,
    ringKrullDim_eq_of_ringEquiv (Spec.stalkIso (.of A) q).commRingCatIsoToRingEquiv]
  have := q.isPrime
  refine (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal _).trans ?_
  rw [height_eq_one_of_mem_minimalPrimes_map_maximalIdeal O hmin]
  rfl
end GlobalTheory
