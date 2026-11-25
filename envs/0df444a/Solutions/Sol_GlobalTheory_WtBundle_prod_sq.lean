-- Prove2me | solution 1 for GlobalTheory.WtBundle.prod_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:01:40.708508+00:00
-- url     : https://prove2.me/submissions/98bb01eb-70f2-4d24-aa13-049f4a0e9e3c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CommGroupCommonFactorQuotientCancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.WtBundle
variable {S : Scheme.{0}}
namespace GlobalTheory.WtBundle
theorem _root_.solution {G T : Over S} [GrpObj G] (x y : T ⟶ G) {U : Type} [CommGroup U] (F : (T ⟶ G) → U) :
    ∏ k, F (sq x y k) ^ Oε k = F (x * y) * (F x)⁻¹ * (F y)⁻¹ * F 1 := by
  rw [Fin.prod_univ_four]
  change F (x * y) ^ (1 : ℤ) * F x ^ (-1 : ℤ) * F y ^ (-1 : ℤ) * F 1 ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one]
end GlobalTheory.WtBundle
