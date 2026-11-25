-- Prove2me | solution 1 for GlobalTheory.SectionsDescent.appLE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:11:42.619706+00:00
-- url     : https://prove2.me/submissions/d5ae5588-9a57-429d-86a4-bffb70d47fff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine

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
noncomputable section
open GlobalTheory GlobalTheory.SectionsDescent
open GlobalTheory.FieldBaseChange
namespace GlobalTheory.SectionsDescent
theorem _root_.solution {X Y : Scheme.{0}} (φ : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (x : Γ(X, U)) :
    (φ.appLE U V h).hom x = rs h ((φ.app U).hom x) := rfl
end GlobalTheory.SectionsDescent
