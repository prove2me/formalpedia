-- Prove2me | solution 1 for GlobalTheory.UU.existsUnique_cubWeil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:04:41.864532+00:00
-- url     : https://prove2.me/submissions/336b6820-8a60-4a50-9b68-5b33e164cfa0

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
import Theorems.Thm_GlobalTheory_UU_CubWeil_unique
import Theorems.Thm_GlobalTheory_UU_cubWeil_iff_isRatio
import Theorems.Thm_GlobalTheory_WeilCube_exists_isRatio
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
theorem _root_.solution (c : CubicalStr G L) (hx : x ^ N = 1) (hy : y ^ N = 1) : ∃! ζ, CubWeil c N x y ζ := by
  obtain ⟨e, he⟩ := WeilCube.exists_isRatio c N x y hx hy
  have h0 : CubWeil c N x y e := cubWeil_iff_isRatio.2 ⟨hx, hy, he⟩
  exact ⟨e, h0, fun ζ hζ => CubWeil.unique hζ h0⟩
end GlobalTheory.UU
