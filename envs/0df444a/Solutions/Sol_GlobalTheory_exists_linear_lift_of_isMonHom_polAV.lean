-- Prove2me | solution 1 for GlobalTheory.exists_linear_lift_of_isMonHom_polAV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:34:53.520375+00:00
-- url     : https://prove2.me/submissions/36a88709-700e-4d71-9583-4c74b324a286

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqZeroOfFderivEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearLiftOfIsMonHomPolAV
import Theorems.Thm_GlobalTheory_HomLinear_exists_linear_of_isMonHom
import Theorems.Thm_GlobalTheory_TorusTransfer_tangent_bijective


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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (P P' : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (L' : LB P'.A.left) (u : HolUnif P.A L P.g) (u' : HolUnif P'.A L' P'.g) (f : P.A ⟶ P'.A), IsMonHom f → ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ), ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro P P' L L' u u' f hf
  obtain ⟨F, hF, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom P.A P'.A P.3 P'.3 L L' P.g P'.g u u'
    (GlobalTheory.TorusTransfer.tangent_bijective u' P'.5).1 (GlobalTheory.TorusTransfer.tangent_bijective u' P'.5).2 f hf
  exact ⟨F, hF⟩
end GlobalTheory
