-- Prove2me | solution 1 for GlobalTheory.KS.DerMor.appLE_app_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:27:19.234479+00:00
-- url     : https://prove2.me/submissions/3cff9653-2388-48ff-bd36-b926fc29f1d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomFromConstThickeningOfDerivation

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
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DerMor
namespace GlobalTheory.KS.DerMor
theorem _root_.solution {Y Y' : Scheme.{0}} (ρ : Y' ⟶ Y) (j : Y ⟶ Y') (h : j ≫ ρ = 𝟙 Y)
    (O : Y.Opens) (e : O ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ O)) (a : Γ(Y, O)) :
    (j.appLE (ρ ⁻¹ᵁ O) O e).hom ((ρ.app O).hom a) = a := by
  have key : ∀ (g : Y ⟶ Y), g = 𝟙 Y → ∀ e' : O ≤ g ⁻¹ᵁ O, (g.appLE O O e').hom a = a := by
    intro g hg e'
    subst hg
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact congrArg (fun φ => φ.hom a) (Y.presheaf.map_id (Opposite.op O))
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact key _ h _
end GlobalTheory.KS.DerMor
