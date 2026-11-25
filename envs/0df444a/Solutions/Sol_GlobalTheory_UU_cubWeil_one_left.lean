-- Prove2me | solution 1 for GlobalTheory.UU.cubWeil_one_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:17:41.021801+00:00
-- url     : https://prove2.me/submissions/b113eb1e-90e0-4191-8a1c-a333fc4d2859

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOneLeft
import Theorems.Thm_GlobalTheory_UU_CubWeil_mul_left
import Theorems.Thm_GlobalTheory_UU_CubWeil_unique
import Theorems.Thm_GlobalTheory_UU_TorusCompat_unique
import Theorems.Thm_GlobalTheory_UU_existsUnique_cubWeil


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
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
  {T : Over S} {x x' y : T ⟶ G}
namespace GlobalTheory.UU
theorem _root_.solution (c : CubicalStr G L) (hy : y ^ N = 1) : CubWeil c N 1 y 1 := by
  obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil (x := (1 : T ⟶ G)) c (one_pow N) hy
  have h2 := hζ.mul_left hζ
  rw [_root_.one_mul] at h2
  have e : ζ * ζ = ζ * 1 := by rw [_root_.mul_one]; exact h2.unique hζ
  rw [mul_left_cancel e] at hζ
  exact hζ
end GlobalTheory.UU
