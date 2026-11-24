-- Prove2me | solution 1 for GlobalTheory.exists_valuationSubring_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:14.907004+00:00
-- url     : https://prove2.me/submissions/69f4e3c9-b10b-4093-9240-23e1e8439e83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Theorems.Thm_GlobalTheory_exists_valuationSubring_lift_of_isOpen
import Theorems.Thm_GlobalTheory_range_specMap_fractionField
import Theorems.Thm_GlobalTheory_isOpenImmersion_specMap_fractionField

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
    {z : Z} (hz : IsClosed ({z} : Set Z)) (hzO : f z = closedPoint O) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (h : O →+* O') (_ : IsLocalHom h)
      (y : Spec (.of O') ⟶ Z)
      (y' : Spec (.of K') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap O K)))),
      (∀ a : O, (h a : K') = algebraMap K K' (algebraMap O K a)) ∧
      y ≫ f = Spec.map (CommRingCat.ofHom h) ∧ y (closedPoint O') = z ∧
      y' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap O' K')) ≫ y ∧
      y' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap K K')) ∧
      ∀ t, y' t ∈ U := by
  have := isOpenImmersion_specMap_fractionField (O := O) (K := K)
  have hemb := (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap O K)))).isOpenEmbedding
  obtain ⟨K', _, _, _, O', h, _, y, hh, hy, hyz, hyW⟩ :=
    exists_valuationSubring_lift_of_isOpen K f (hemb.isOpenMap U hU) (fun x hx => by
      have : x ∈ Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap O K)))) := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, range_specMap_fractionField]
        exact hx
      obtain ⟨x, rfl⟩ := this
      exact image_closure_subset_closure_image hemb.continuous ⟨x, hd x, rfl⟩) hz hzO
  have hcomm : (Spec.map (CommRingCat.ofHom (algebraMap O' K')) ≫ y) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap O K)) := by
    rw [Category.assoc, hy, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact hh a
  refine ⟨K', inferInstance, inferInstance, inferInstance, O', h, inferInstance, y,
    pullback.lift _ _ hcomm, hh, hy, hyz, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
    fun t => ?_⟩
  obtain ⟨x, hxU, hx⟩ := hyW t
  rw [← pullback.lift_fst _ _ hcomm, Scheme.Hom.comp_apply] at hx
  exact hemb.injective hx ▸ hxU
end GlobalTheory
