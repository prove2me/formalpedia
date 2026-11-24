-- Prove2me | solution 1 for GlobalTheory.EpsCocycle.pullLE_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:40:58.636545+00:00
-- url     : https://prove2.me/submissions/ff85c872-380e-4828-96f6-28b65b65c80f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleCocycleOneAddEps
import Theorems.Thm_GlobalTheory_EpsCocycle_appLE_section

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
    (a : Γ(Y, O)ˣ) : pullLE j h' (pullLE ρ h a) = res h'' a := by
  ext
  exact appLE_section hj h h' h'' a.val
end GlobalTheory.EpsCocycle
