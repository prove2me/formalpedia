-- Prove2me | solution 1 for GlobalTheory.isEmbedding_and_range_eq_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:39.405899+00:00
-- url     : https://prove2.me/submissions/a87304c2-ccda-4088-90c6-bea9dd13fc49

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
omit [IsDomain O] [IsDiscreteValuationRing O] [IsIntegral Y] [LocallyOfFiniteType f] [Flat f]
namespace GlobalTheory
theorem _root_.solution {T P : Scheme.{u}} {g : T ⟶ Spec (.of O)}
    [IsPreimmersion g] {i : P ⟶ Y} {p : P ⟶ T} (h : IsPullback i p f g) :
    IsEmbedding i ∧ Set.range i = f ⁻¹' Set.range g := by
  have : IsPreimmersion i := MorphismProperty.of_isPullback h.flip inferInstance
  refine ⟨i.isEmbedding, ?_⟩
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]
end GlobalTheory
