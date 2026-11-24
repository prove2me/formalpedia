-- Prove2me | solution 1 for GlobalTheory.MatrixPower.prod_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:54:27.290403+00:00
-- url     : https://prove2.me/submissions/f243d1fa-d225-40ba-af97-b02886f89885

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AbelianSchemeEighthPowerOfMatrixAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.MatrixPower
variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
variable [BraidedCategory C]
namespace GlobalTheory.MatrixPower
theorem _root_.solution {n : Type*} (s : Finset n) {T G H : C} [GrpObj G] [IsCommMonObj G]
    [GrpObj H] [IsCommMonObj H] (g : n → (T ⟶ G)) (f : G ⟶ H) [IsMonHom f] :
    (∏ u ∈ s, g u) ≫ f = ∏ u ∈ s, g u ≫ f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]
end GlobalTheory.MatrixPower
