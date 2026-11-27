-- Prove2me | solution 1 for GlobalTheory.topologicalKrullDim_component_fiber_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:02.431676+00:00
-- url     : https://prove2.me/submissions/7515f620-94d8-4814-a08f-78dea4e87a87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Theorems.Thm_GlobalTheory_exists_topologicalKrullDim_fibres_eq_of_isEmbedding

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
theorem _root_.solution {Z : Set (f.fiber (closedPoint O))}
    (hZ : Z ∈ irreducibleComponents (f.fiber (closedPoint O))) :
    topologicalKrullDim Z = topologicalKrullDim (f.fiber (genericPoint (Spec (.of O)))) := by
  obtain ⟨d, h₁, h₂⟩ := exists_topologicalKrullDim_fibres_eq_of_isEmbedding f
    (f.fiberι _).isEmbedding (f.range_fiberι _) (f.fiberι _).isEmbedding (f.range_fiberι _)
  rw [h₁, h₂ Z hZ]
end GlobalTheory
