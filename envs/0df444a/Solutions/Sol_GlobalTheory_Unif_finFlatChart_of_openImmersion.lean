-- Prove2me | solution 1 for GlobalTheory.Unif.finFlatChart_of_openImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:16:07.345072+00:00
-- url     : https://prove2.me/submissions/79409d57-7291-426c-a9e1-4a3bf4776887

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FinFlatChartOfOpenImmersion
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct
open GlobalTheory GlobalTheory.Unif
namespace GlobalTheory.Unif
theorem _root_.solution {X Y Z S B : Scheme.{0}} (f : X ⟶ B) (s : S ⟶ B)
    (j : Y ⟶ X) [IsOpenImmersion j] (i : Z ⟶ S) [IsOpenImmersion i] (p : Y ⟶ Z)
    [IsFinite p] [Flat p] [Surjective p] [Nonempty Z] (h : p ≫ i ≫ s = j ≫ f) :
    ∃ (W : X.Opens) (V : S.Opens) (π : W.toScheme ⟶ V.toScheme), (W : Set X).Nonempty ∧
      IsFinite π ∧ Flat π ∧ Surjective π ∧ π ≫ V.ι ≫ s = W.ι ≫ f := by
  obtain ⟨y, -⟩ := p.surjective (Classical.arbitrary Z)
  refine ⟨j.opensRange, i.opensRange, j.isoOpensRange.inv ≫ p ≫ i.isoOpensRange.hom,
    ⟨j y, y, rfl⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, h]
  rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι_assoc]
end GlobalTheory.Unif
