-- Prove2me | solution 1 for GlobalTheory.UU.cubN_ratio_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:26:51.02085+00:00
-- url     : https://prove2.me/submissions/bacd5fe2-5ac5-4e0a-8a27-2ef1d7ae5034

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubNRatioTwist
import Theorems.Thm_GlobalTheory_UU_cubN_twist

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
theorem _root_.solution {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (β : A' →* A) (W : A' → U)
    {θ : A → A → A → U} {θ' : A' → A' → A' → U}
    (hθ : ∀ a b d, θ (β a) (β b) (β d) * W (a * b) * W (a * d) * W (b * d) * W 1 =
      W (a * b * d) * W a * W b * W d * θ' a b d) {x y : A'} {N : ℕ} (hx : x ^ N = 1) (hy : y ^ N = 1) {e : U}
    (h : e * cubN θ' N 1 x y = cubN θ' N 1 y x) :
    e * cubN θ N 1 (β x) (β y) = cubN θ N 1 (β y) (β x) := by
  have h₁ := cubN_twist β W hθ x y N
  have h₂ := cubN_twist β W hθ y x N
  simp only [hx, _root_.one_mul] at h₁
  simp only [hy, _root_.one_mul] at h₂
  rw [mul_comm y x, mul_comm (W y) (W x)] at h₂
  have k₁ : cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N =
      (W x * W y) ^ N * cubN θ' N 1 x y := by
    apply mul_right_cancel (b := W 1 * W y)
    calc cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N * (W 1 * W y)
          = cubN θ N 1 (β x) (β y) * W 1 * W y * (W (x * y) * W 1) ^ N := by ac_rfl
      _ = W y * W 1 * (W x * W y) ^ N * cubN θ' N 1 x y := h₁
      _ = (W x * W y) ^ N * cubN θ' N 1 x y * (W 1 * W y) := by ac_rfl
  have k₂ : cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N =
      (W x * W y) ^ N * cubN θ' N 1 y x := by
    apply mul_right_cancel (b := W 1 * W x)
    calc cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N * (W 1 * W x)
          = cubN θ N 1 (β y) (β x) * W 1 * W x * (W (x * y) * W 1) ^ N := by ac_rfl
      _ = W x * W 1 * (W x * W y) ^ N * cubN θ' N 1 y x := h₂
      _ = (W x * W y) ^ N * cubN θ' N 1 y x * (W 1 * W x) := by ac_rfl
  apply mul_right_cancel (b := (W (x * y) * W 1) ^ N)
  calc e * cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N
        = e * (cubN θ N 1 (β x) (β y) * (W (x * y) * W 1) ^ N) := mul_assoc _ _ _
    _ = (W x * W y) ^ N * (e * cubN θ' N 1 x y) := by rw [k₁]; ac_rfl
    _ = cubN θ N 1 (β y) (β x) * (W (x * y) * W 1) ^ N := by rw [h, k₂]
end GlobalTheory.UU
