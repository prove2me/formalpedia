-- Prove2me | solution 1 for GlobalTheory.PhiBase.prod_comp_fam_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:08:42.138099+00:00
-- url     : https://prove2.me/submissions/91e3149e-16ff-4392-8f3b-1ec8ea05a5a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EqOfIsGenTransl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_DegPreAbelianPartIsIntegralAndIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsThetaPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitOfStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AbelianPartEqOfThetaOperatorEq
import Theorems.Thm_GlobalTheory_ThetaPow_prod_fam_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PhiBase
namespace GlobalTheory.PhiBase
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (t : DegPre.BF D F ⟶ DegPre.BF D F) {U : Type} [CommGroup U]
    (h : ((DegPre.BF D F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (t.left ≫ DegPre.famφ D F 0 i) ^ DegPre.famε k i = h (t ≫ DegPre.prB D F).left ^ k :=
  ThetaPow.prod_fam_zero D F k (fun q => h (t.left ≫ q))
end GlobalTheory.PhiBase
