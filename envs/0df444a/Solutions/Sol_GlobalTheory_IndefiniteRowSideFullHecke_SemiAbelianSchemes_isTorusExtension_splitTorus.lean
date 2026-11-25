-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes.isTorusExtension_splitTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:40.346802+00:00
-- url     : https://prove2.me/submissions/95a95145-68d2-4a19-905a-d797de8f97cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemiAbelianSchemes_isAbelianScheme_unit
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemiAbelianSchemes_flat_splitTorusAff
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemiAbelianSchemes_finitePresentation_splitTorusAff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
open ReciprocityTheory.ChartRestriction.G.Semi
variable (X : Type u) [AddCommGroup X]
namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
theorem _root_.solution (k : Type u) [Field k] [Module.Free ℤ X] [Module.Finite ℤ X] :
    IsTorusExtension (splitTorus (Spec (CommRingCat.of k)) X) := by
  have hc : IsCommMonObj (splitTorus (Spec (CommRingCat.of k)) X) := by
    unfold splitTorus; infer_instance
  have h1 := flat_splitTorusAff X
  have h2 := finitePresentation_splitTorusAff X
  have e : (toUnit (splitTorus (Spec (CommRingCat.of k)) X)).left =
      (splitTorus (Spec (CommRingCat.of k)) X).hom := by
    simpa using Over.w (toUnit (splitTorus (Spec (CommRingCat.of k)) X))
  refine ⟨hc, X, inferInstance, inferInstance, inferInstance, 𝟙_ _, inferInstance, 𝟙 _,
    toUnit _, isAbelianScheme_unit _, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · have : IsIso (η : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ 𝟙_ _) := by
      rw [toUnit_unique (η : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ 𝟙_ _) (𝟙 _)]
      infer_instance
    exact IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩
  · rw [e]; exact inferInstanceAs (Flat (pullback.snd _ _))
  · rw [e]
    exact ⟨fun y => ⟨(η : 𝟙_ _ ⟶ splitTorus (Spec (CommRingCat.of k)) X).left y, by
      rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  · rw [e]; exact inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _))
end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
