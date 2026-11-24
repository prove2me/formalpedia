-- Prove2me | solution 1 for GlobalTheory.splitTorus_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:42.726261+00:00
-- url     : https://prove2.me/submissions/889be861-4858-43f1-8dc2-f4f7ebe1b0a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Theorems.Thm_GlobalTheory_exists_pullback_comp_iso_monHom
import Theorems.Thm_GlobalTheory_charUnit_val_eq_appTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] :
    ∃ e : splitTorus S' X ≅ (Over.pullback f).obj (splitTorus S X), IsMonHom e.hom ∧
      ∀ χ : X, (e.hom.left ≫ pullback.fst (splitTorus S X).hom f).appTop.hom (charUnit S X χ).val =
        (charUnit S' X χ).val := by
  obtain ⟨e, he, hf⟩ := exists_pullback_comp_iso_monHom f (toZ S) (toZ S')
    (specULiftZIsTerminal.hom_ext _ _) (splitTorusAff ZU X)
  refine ⟨e, he, fun χ => ?_⟩
  rw [charUnit_val_eq_appTop, charUnit_val_eq_appTop, ← hf, ← Category.assoc]
  simp only [Scheme.Hom.comp_appTop]
  rfl
end GlobalTheory
