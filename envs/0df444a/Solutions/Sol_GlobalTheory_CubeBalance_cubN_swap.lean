-- Prove2me | solution 1 for GlobalTheory.CubeBalance.cubN_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:42:53.970489+00:00
-- url     : https://prove2.me/submissions/231c25b1-91a2-4978-affd-cdc8a5c894d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Theorems.Thm_GlobalTheory_CubeBalance_cubN_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.CubeBalance
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
namespace GlobalTheory.CubeBalance
theorem _root_.solution (h : IsCub θ) (a b : ℕ) (x y : A) :
    cubN θ a 1 x (y ^ b) * cubN θ b 1 y x ^ a = cubN θ b 1 y (x ^ a) * cubN θ a 1 x y ^ b := by
  induction b with
  | zero =>
    rw [pow_zero, h.N_one]
    simp [cubN]
  | succ b ih =>
    have n := h.N_add a 1 x (y ^ b) y
    rw [h.face, _root_.mul_one, _root_.one_mul] at n
    have r : ∀ z : A, θ (y ^ b) y z = θ z (y ^ b) y := fun z => by rw [h.s12, h.s01]
    rw [cubN_succ, cubN_succ, r, r, pow_succ y, mul_pow, pow_succ, mul_comm (cubN θ b 1 y x ^ a),
      ← _root_.mul_assoc, n]
    calc θ (x ^ a) (y ^ b) y * cubN θ a 1 x (y ^ b) * cubN θ a 1 x y * cubN θ b 1 y x ^ a
        = θ (x ^ a) (y ^ b) y * cubN θ a 1 x y * (cubN θ a 1 x (y ^ b) * cubN θ b 1 y x ^ a) := by ac_rfl
      _ = _ := by rw [ih]; ac_rfl
end GlobalTheory.CubeBalance
