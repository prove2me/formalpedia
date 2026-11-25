-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.isAddLawHom_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:14:37.181603+00:00
-- url     : https://prove2.me/submissions/7cbd0ba9-bf1c-41ba-942a-dc4a742d84a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HomExtOfLocalRingPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsEqPtHomOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_ExistsGrpObjIsAddLawHom

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : _root_.WeierstrassCurve R)
variable [W.IsElliptic]
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution : IsAddLawHom W μ[schemeOver W] := by
  intro A _ ρ P Q T hP hQ hT h x y hx hy
  let : Algebra R A := ρ.toAlgebra
  obtain rfl : x = ptOver W (A := A) P hP := Over.OverMorphism.ext hx
  obtain rfl : y = ptOver W (A := A) Q hQ := Over.OverMorphism.ext hy
  exact congrArg (·.left) (ptOver_mul_ptOver W (A := A) hP hQ hT ⟨h.1, h.2⟩)
end GlobalTheory.WeierstrassCurve
