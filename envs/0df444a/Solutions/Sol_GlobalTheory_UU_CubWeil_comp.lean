-- Prove2me | solution 1 for GlobalTheory.UU.CubWeil.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:21:15.187831+00:00
-- url     : https://prove2.me/submissions/7818a8c3-48b8-4e3e-aa20-b59ded92224c

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
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_cubWeil_iff_isRatio
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
namespace CubWeil
theorem _root_.solution {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) {T' : Over S} (σ : T' ⟶ T) :
    CubWeil c N (σ ≫ x) (σ ≫ y) (Units.map σ.left.appTop.hom.toMonoidHom ζ) := by
  obtain ⟨hx, hy, hr⟩ := cubWeil_iff_isRatio.1 h
  have hp : ∀ a : T ⟶ G, a ^ N = 1 → (σ ≫ a) ^ N = 1 := fun a ha => by
    rw [← MonObj.comp_pow, ha, MonObj.comp_one]
  exact cubWeil_iff_isRatio.2 ⟨hp x hx, hp y hy, WeilCube.IsRatio.comp c hr σ⟩
end CubWeil
end GlobalTheory.UU
