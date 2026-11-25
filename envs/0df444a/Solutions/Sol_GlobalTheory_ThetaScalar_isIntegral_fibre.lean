-- Prove2me | solution 1 for GlobalTheory.ThetaScalar.isIntegral_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:36.546811+00:00
-- url     : https://prove2.me/submissions/d334a1f0-d9ee-45b0-b8ae-2480f59db252

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Theorems.Thm_GlobalTheory_geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaScalar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {S : Scheme.{0}} {F : Type} [Field F]
namespace GlobalTheory.ThetaScalar
theorem _root_.solution (P : PolAV S) (t : Sp F ⟶ S) : IsIntegral (Over.mk t ⊗ P.A).left :=
  haveI := P.isAb.smooth
  haveI := P.isAb.geomConnected
  (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom).geometrically_isIntegral t _ _
    (IsPullback.of_hasPullback t P.A.hom).flip
end GlobalTheory.ThetaScalar
