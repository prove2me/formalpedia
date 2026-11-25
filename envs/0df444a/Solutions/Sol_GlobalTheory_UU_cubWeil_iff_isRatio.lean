-- Prove2me | solution 1 for GlobalTheory.UU.cubWeil_iff_isRatio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:05:57.783247+00:00
-- url     : https://prove2.me/submissions/2677ef5c-b799-4459-ba94-ec3b0e40832e

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
theorem _root_.solution {ζ : Γ(T.left, ⊤)ˣ} :
    CubWeil c N x y ζ ↔ x ^ N = 1 ∧ y ^ N = 1 ∧ WeilCube.IsRatio c N x y ζ := by
  have at1 : ∀ {e : Γ(T.left, ⊤)ˣ}, WeilCube.IsRatio c N x y e → ∀ (z : T.left) (J), Good L.L z J →
      gm (𝟙 T.left) z ⊤ e * cubN (cubV c z J) N 1 x y = cubN (cubV c z J) N 1 y x := by
    intro e he z J hJ
    simpa only [Over.id_left, Category.id_comp] using he T (𝟙 T) z J hJ
  constructor
  · rintro ⟨hx, hy, h⟩
    obtain ⟨e, he⟩ := WeilCube.exists_isRatio c N x y hx hy
    have hζ : ζ = e := CubWeil.unique ⟨hx, hy, h⟩ ⟨hx, hy, at1 he⟩
    exact ⟨hx, hy, hζ ▸ he⟩
  · rintro ⟨hx, hy, h⟩
    exact ⟨hx, hy, at1 h⟩
end GlobalTheory.UU
