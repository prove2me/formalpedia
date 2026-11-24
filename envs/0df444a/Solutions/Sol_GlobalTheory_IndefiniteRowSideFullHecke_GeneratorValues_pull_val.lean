-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.pull_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:40:17.224503+00:00
-- url     : https://prove2.me/submissions/8f7eaec9-5278-4a2a-80f4-642f2412dc8c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
theorem _root_.solution {X : Scheme.{0}} {S T : CommRingCat.{0}} (φ : S ⟶ T) (c : Spec S ⟶ X)
    (U : X.Opens) (g : Γ(X, U)ˣ) (h : ⊤ ≤ c ⁻¹ᵁ U) (h' : ⊤ ≤ (Spec.map φ ≫ c) ⁻¹ᵁ U) :
    Units.map (Scheme.ΓSpecIso T).hom.hom.toMonoidHom (res h' (pullU (Spec.map φ ≫ c) U g)) =
      Units.map φ.hom.toMonoidHom
        (Units.map (Scheme.ΓSpecIso S).hom.hom.toMonoidHom (res h (pullU c U g))) := by
  ext
  change ((Spec.map φ ≫ c).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso T).hom).hom g.val =
    (c.appLE U ⊤ h ≫ (Scheme.ΓSpecIso S).hom ≫ φ).hom g.val
  rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]
  rfl
end GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
