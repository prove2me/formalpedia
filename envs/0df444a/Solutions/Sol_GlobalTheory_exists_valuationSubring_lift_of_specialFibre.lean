-- Prove2me | solution 1 for GlobalTheory.exists_valuationSubring_lift_of_specialFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:29.991318+00:00
-- url     : https://prove2.me/submissions/40f69267-ca92-487b-a31e-558b86cce963

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Theorems.Thm_GlobalTheory_exists_valuationSubring_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {O K : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]
namespace GlobalTheory
theorem _root_.solution {Z : Scheme.{u}} (f : Z ⟶ Spec (.of O))
    [Flat f] [LocallyOfFiniteType f]
    {U : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap O K))))}
    (hU : IsOpen U) (hd : Dense U)
    {z : ↥(pullback f (Spec.map (CommRingCat.ofHom (residue O))))}
    (hz : IsClosed ({z} : Set _)) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (h : O →+* O') (_ : IsLocalHom h)
      (y : Spec (.of O') ⟶ Z)
      (y' : Spec (.of K') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap O K)))),
      (∀ a : O, (h a : K') = algebraMap K K' (algebraMap O K a)) ∧
      y ≫ f = Spec.map (CommRingCat.ofHom h) ∧
      y (closedPoint O') = pullback.fst f (Spec.map (CommRingCat.ofHom (residue O))) z ∧
      y' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap O' K')) ≫ y ∧
      y' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap K K')) ∧
      ∀ t, y' t ∈ U := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (residue O))) :=
    IsClosedImmersion.spec_of_surjective _ residue_surjective
  refine exists_valuationSubring_lift f hU hd ?_ ?_
  · rw [← Set.image_singleton]
    exact (pullback.fst f (Spec.map (CommRingCat.ofHom (residue O)))).isClosedEmbedding.isClosedMap
      _ hz
  · rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact PrimeSpectrum.comap_residue O _
end GlobalTheory
