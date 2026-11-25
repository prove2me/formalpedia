-- Prove2me | solution 1 for GlobalTheory.UU.CubWeil.mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:45:22.776536+00:00
-- url     : https://prove2.me/submissions/1d2d9b9c-8f22-4528-aa81-dc86153fbd32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOneLeft
import Theorems.Thm_GlobalTheory_UU_cubN_mul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
private theorem gm_id_global_mul {X : Scheme.{0}} (z : X) (a b : Γ(X, ⊤)ˣ) :
    gm (𝟙 X) z ⊤ (a * b) = gm (𝟙 X) z ⊤ a * gm (𝟙 X) z ⊤ b :=
  map_mul _ a b
section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
  {T : Over S} {x x' y : T ⟶ G}
end
end GlobalTheory.UU
end
end

set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
  {T : Over S} {x x' y : T ⟶ G}
namespace GlobalTheory.UU
namespace CubWeil
theorem _root_.solution {ζ ζ' : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (h' : CubWeil c N x' y ζ') :
    CubWeil c N (x * x') y (ζ * ζ') := by
  obtain ⟨hx, hy, hv⟩ := h
  obtain ⟨hx', -, hv'⟩ := h'
  refine ⟨by rw [mul_pow, hx, hx', _root_.one_mul], hy, fun z J hJ => ?_⟩
  have hc := isCub_cubV c hJ
  have e1 := cubN_mul_left hc N x x' y
  rw [hx, hx', hc.face, _root_.one_mul, hc.s12 x x' y, hc.s01 x y x'] at e1
  have e2 := hc.N_add N 1 y x x'
  simp only [hc.face, _root_.one_mul, _root_.mul_one, hy] at e2
  apply mul_right_cancel (b := cubV c z J y x x' ^ N)
  rw [gm_id_global_mul, _root_.mul_assoc, e1, e2, ← hv z J hJ, ← hv' z J hJ]
  exact mul_mul_mul_comm _ _ _ _
end CubWeil
end GlobalTheory.UU
