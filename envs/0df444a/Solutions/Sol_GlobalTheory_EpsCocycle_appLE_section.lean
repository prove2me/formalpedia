-- Prove2me | solution 1 for GlobalTheory.EpsCocycle.appLE_section
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:08.530148+00:00
-- url     : https://prove2.me/submissions/cae823c3-cfae-4eb2-89cb-149f4aea880a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleCocycleOneAddEps

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.EpsCocycle
noncomputable section
namespace GlobalTheory.EpsCocycle
theorem _root_.solution {Y Y' : Scheme.{0}} {ρ : Y' ⟶ Y} {j : Y ⟶ Y'} (hj : j ≫ ρ = 𝟙 Y)
    {O O₂ : Y.Opens} {O' : Y'.Opens} (h : O' ≤ ρ ⁻¹ᵁ O) (h' : O₂ ≤ j ⁻¹ᵁ O') (h'' : O₂ ≤ O)
    (a : Γ(Y, O)) :
    (j.appLE O' O₂ h').hom ((ρ.appLE O O' h).hom a) = resG Y h'' a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (f : Y ⟶ Y) (_ : f = 𝟙 Y) (e : O₂ ≤ f ⁻¹ᵁ O), (f.appLE O O₂ e).hom a = resG Y h'' a := by
    intro f hf e
    subst hf
    simp [Scheme.Hom.appLE]
    rfl
  exact key _ hj _
end GlobalTheory.EpsCocycle
