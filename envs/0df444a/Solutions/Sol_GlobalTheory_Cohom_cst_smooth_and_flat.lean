-- Prove2me | solution 1 for GlobalTheory.Cohom.cst_smooth_and_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:19.605457+00:00
-- url     : https://prove2.me/submissions/954c9c90-6c7e-42e2-b2a7-8a05f03729e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CstSmoothAndFlat
import Theorems.Thm_GlobalTheory_IsGradedMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.Cohom
namespace GlobalTheory.Cohom
theorem _root_.solution : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (V : Y.Opens), IsAffineOpen V → (Smooth f → (cst f V).Smooth) ∧ (Flat f → (cst f V).Flat) := by
  intro R _ Y f V hV
  have e : cst f V = (f.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := rfl
  have hb : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  rw [e]
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · exact (RingHom.Smooth.of_bijective hb).comp (f.smooth_appLE (isAffineOpen_top _) hV le_top)
  · exact (RingHom.Flat.of_bijective hb).comp (f.flat_appLE (isAffineOpen_top _) hV le_top)
end GlobalTheory.Cohom
