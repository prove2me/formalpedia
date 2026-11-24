-- Prove2me | solution 1 for GlobalTheory.KS.DerMorK.app_constFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:26:04.685077+00:00
-- url     : https://prove2.me/submissions/8491ca03-3cc1-45d1-b3b6-0e3aa275397b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomOfDerivation
import Theorems.Thm_GlobalTheory_KS_DerMorK_appLE_constFn

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DerMorK
namespace GlobalTheory.KS.DerMorK
theorem _root_.solution {R : Type} [CommRing R] {Z X : Scheme.{0}} (f : Z ⟶ X) (p : X ⟶ Sp R)
    (U : X.Opens) (a : R) :
    (f.app U).hom (constFn p U a) = constFn (f ≫ p) (f ⁻¹ᵁ U) a := by
  rw [Scheme.Hom.app_eq_appLE, appLE_constFn]
end GlobalTheory.KS.DerMorK
