-- Prove2me | solution 1 for GlobalTheory.UU.cubN_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:17.615916+00:00
-- url     : https://prove2.me/submissions/db2965a0-c682-40b8-9368-a3e9a2d1b6d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubNRatioTwist

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
      W (a * b * d) * W a * W b * W d * θ' a b d) (x y : A') (k : ℕ) :
    cubN θ k 1 (β x) (β y) * W (x ^ k) * W y * (W (x * y) * W 1) ^ k =
      W (x ^ k * y) * W 1 * (W x * W y) ^ k * cubN θ' k 1 x y := by
  induction k with
  | zero => simp only [cubN, Finset.range_zero, Finset.prod_empty, pow_zero, _root_.one_mul, _root_.mul_one]; exact mul_comm _ _
  | succ k ih =>
    have e₁ : cubN θ (k + 1) 1 (β x) (β y) = cubN θ k 1 (β x) (β y) * θ (β (x ^ k)) (β x) (β y) := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, map_pow]
    have e₂ : cubN θ' (k + 1) 1 x y = cubN θ' k 1 x y * θ' (x ^ k) x y := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have H := hθ (x ^ k) x y
    rw [← pow_succ] at H
    rw [e₁, e₂]
    apply mul_right_cancel (b := W (x ^ k) * W (x ^ k * y))
    calc cubN θ k 1 (β x) (β y) * θ (β (x ^ k)) (β x) (β y) * W (x ^ (k + 1)) * W y *
            (W (x * y) * W 1) ^ (k + 1) * (W (x ^ k) * W (x ^ k * y))
          = (cubN θ k 1 (β x) (β y) * W (x ^ k) * W y * (W (x * y) * W 1) ^ k) *
            (θ (β (x ^ k)) (β x) (β y) * W (x ^ (k + 1)) * W (x ^ k * y) * W (x * y) * W 1) := by
          rw [pow_succ (W (x * y) * W 1) k]; ac_rfl
      _ = (W (x ^ k * y) * W 1 * (W x * W y) ^ k * cubN θ' k 1 x y) *
            (W (x ^ (k + 1) * y) * W (x ^ k) * W x * W y * θ' (x ^ k) x y) := by rw [ih, H]
      _ = W (x ^ (k + 1) * y) * W 1 * (W x * W y) ^ (k + 1) * (cubN θ' k 1 x y * θ' (x ^ k) x y) *
            (W (x ^ k) * W (x ^ k * y)) := by
          rw [pow_succ (W x * W y) k]; ac_rfl
end GlobalTheory.UU
