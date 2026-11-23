-- Prove2me | solution 1 for GlobalTheory.FinAffineCharts.res_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:18.1938+00:00
-- url     : https://prove2.me/submissions/cdea4e53-9e5f-4720-9d34-9d4a19debad9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteAffineCharts

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
open GlobalTheory GlobalTheory.FinAffineCharts
variable {X : Scheme.{0}}
namespace GlobalTheory.FinAffineCharts
theorem _root_.solution {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)ˣ) :
    res h₂ (res h₁ s) = res (h₂.trans h₁) s := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
    (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl
end GlobalTheory.FinAffineCharts
