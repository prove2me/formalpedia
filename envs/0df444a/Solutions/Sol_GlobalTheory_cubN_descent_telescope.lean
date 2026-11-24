-- Prove2me | solution 1 for GlobalTheory.cubN_descent_telescope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:58.519838+00:00
-- url     : https://prove2.me/submissions/54f50eab-0e78-42d3-b7a9-fb53afeb8f28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubNDescentTelescope
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339


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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (θ : A → A → A → U)
    (θ' : A' → A' → A' → U) (q : A →* A') (W : A → U) (hc : IsCub θ')
    (h : ∀ x y u, θ' (q x) (q y) (q u) * W (x * y) * W (x * u) * W (y * u) * W 1 =
      W (x * y * u) * W x * W y * W u * θ x y u) (k : ℕ) (x y : A) (hx : q x = 1) :
    cubN θ k 1 x y * W (x ^ k * y) * W x ^ k * W y ^ k * W 1 = W (x ^ k) * W y * W (x * y) ^ k * W 1 ^ k := by
  induction k with
  | zero => simp [cubN, mul_comm]
  | succ k ih =>
    have e := h (x ^ k) x y
    rw [hx, hc.face₂, _root_.one_mul, ← pow_succ] at e
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ (W x), pow_succ (W y), pow_succ (W (x * y)), pow_succ (W 1)]
    generalize (∏ i ∈ Finset.range k, θ (x ^ i) x y) = P at ih ⊢
    apply Additive.ofMul.injective
    have a1 := congrArg Additive.ofMul ih
    have a2 := congrArg Additive.ofMul e
    simp only [ofMul_mul] at a1 a2 ⊢
    linear_combination (norm := abel) a1 - a2
end GlobalTheory
