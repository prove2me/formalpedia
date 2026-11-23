-- Prove2me | solution 1 for GlobalTheory.isClosed_image_of_mem_irreducibleComponents
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:42.744669+00:00
-- url     : https://prove2.me/submissions/b3ea7c42-95a1-4013-9865-45045c16998f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes

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
omit [IsIntegral Y] [LocallyOfFiniteType f] [Flat f]
namespace GlobalTheory
theorem _root_.solution {S : Type*} [TopologicalSpace S]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {Z : Set S} (hZ : Z ∈ irreducibleComponents S) : IsClosed (i '' Z) := by
  have : IsClosedEmbedding i := ⟨hi, hr ▸ (isClosed_singleton_closedPoint O).preimage f.continuous⟩
  exact this.isClosedMap _ (isClosed_of_mem_irreducibleComponents Z hZ)
end GlobalTheory
