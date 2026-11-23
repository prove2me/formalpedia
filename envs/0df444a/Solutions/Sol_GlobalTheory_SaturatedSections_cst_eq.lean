-- Prove2me | solution 1 for GlobalTheory.SaturatedSections.cst_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:15.195158+00:00
-- url     : https://prove2.me/submissions/b2c10265-c51d-4ba7-9e14-ad572eaadeb0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueCombOfIndependentSpecialFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SaturatedSections
namespace GlobalTheory.SaturatedSections
theorem _root_.solution {W : Type} [CommRing W] {H : Scheme.{0}} (p : H ⟶ Sp W) (U : H.Opens) (a : W) :
    Out.resTop U (Out.scal p a) = cst p U a := rfl
end GlobalTheory.SaturatedSections
