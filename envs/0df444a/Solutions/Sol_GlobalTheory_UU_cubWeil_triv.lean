-- Prove2me | solution 1 for GlobalTheory.UU.cubWeil_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:48:08.248798+00:00
-- url     : https://prove2.me/submissions/234bceac-2e26-4908-aa09-36f93837eaaa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm


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
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}}
attribute [instance] TQ.grp TQ.comm
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
  {T : Over S} {x y : T ⟶ G}
namespace GlobalTheory.UU
theorem _root_.solution (hx : x ^ N = 1) (hy : y ^ N = 1) : CubWeil (trivCub G) N x y 1 := by
  refine ⟨hx, hy, fun z J _ => ?_⟩
  simp only [cubN, cubV_trivCub, Finset.prod_const_one, map_one, _root_.one_mul]
end GlobalTheory.UU
