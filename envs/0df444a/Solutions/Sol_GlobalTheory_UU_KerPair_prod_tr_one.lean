-- Prove2me | solution 1 for GlobalTheory.UU.KerPair.prod_tr_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:28:53.817812+00:00
-- url     : https://prove2.me/submissions/a9517fe9-5ea6-425e-b3e7-cbe50540e80e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOfGen
import Theorems.Thm_GlobalTheory_UU_KerPair_prod_tr

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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.KerPair
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B} (c : CubicalStr B L)
  {T : Over S} {x : T ⟶ B}
omit [IsCommMonObj B]
namespace GlobalTheory.UU.KerPair
theorem _root_.solution {T' : Over S} (ρ : T' ⟶ T) (b : T' ⟶ B) {U : Type} [CommGroup U] (h : (T'.left ⟶ B.left) → U) :
    ∏ k : Fin 2, h ((lift ρ b).left ≫ trφ x k) ^ (![1, -1] : Fin 2 → ℤ) k =
      h ((ρ ≫ x) * b).left * (h b.left)⁻¹ := by
  simpa using prod_tr (x := x) ρ b h 1
end GlobalTheory.UU.KerPair
