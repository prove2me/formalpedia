-- Prove2me | solution 1 for GlobalTheory.UU.cubWeil_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:08:31.915051+00:00
-- url     : https://prove2.me/submissions/c44a00c5-4668-47f4-83fc-091eaa69394b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubNRatioTwist
import Theorems.Thm_GlobalTheory_UU_cubN_ratio_twist
import Theorems.Thm_GlobalTheory_UU_IsWt_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution : (∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (P : CP G) (P' : CP G') (F : G'.left ⟶ G.left) (hw) (w), IsCPMap P' P f F hw w → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil P'.c N x y ζ → CubWeil P.c N (toBase hw x) (toBase hw y) ζ) := by
  intro S S' f G _ _ G' _ _ P P' F hw w hP N T x y ζ hζ
  obtain ⟨hx, hy, hr⟩ := hζ
  let β := toBaseHom (hw := hw) hP.mul T
  have hβ : ∀ a : T ⟶ G', β a = toBase hw a := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hβ, ← map_pow, hx, map_one]
  · rw [← hβ, ← map_pow, hy, map_one]
  · intro z J hJ
    obtain ⟨J', hJ'⟩ := exists_good_pt P'.L.isLB z
    have hv := (hP.vals T z J' J hJ' hJ (fun a => gw w a.left z (J (a.left ≫ F)) (J' a.left))
      (fun _ => rfl)).2.2
    exact cubN_ratio_twist β (fun a => gw w a.left z (J (a.left ≫ F)) (J' a.left))
      (θ := cubV P.c (T := Over.mk (T.hom ≫ f)) z J) (θ' := cubV P'.c z J') hv hx hy (hr z J' hJ')
end GlobalTheory.UU
