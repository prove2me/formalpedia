-- Prove2me | solution 1 for GlobalTheory.GlobalFunctions.appTop_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:35.077382+00:00
-- url     : https://prove2.me/submissions/21f6fcce-8a2b-40d3-8c9a-0e1df7501c4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GlobalFunctions
variable {R B C : CommRingCat.{0}} {X : Scheme.{0}}
namespace GlobalTheory.GlobalFunctions
theorem _root_.solution {p : X ⟶ Spec R} {i : Spec B ⟶ X} {φ : R ⟶ B}
    (hφ : i ≫ p = Spec.map φ) :
    p.appTop ≫ i.appTop ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso R).hom ≫ φ := by
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hφ, Scheme.ΓSpecIso_naturality]
end GlobalTheory.GlobalFunctions
