-- Prove2me | solution 1 for GlobalTheory.Ex.NumB.cubN_inv_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:11:53.813378+00:00
-- url     : https://prove2.me/submissions/3f3b868c-516e-43d2-9a21-f16667df4cf1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
import Theorems.Thm_GlobalTheory_CubeBalance_cubN_succ


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
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumB
variable {O : Type} [CommRing O] (B : NumB O)
namespace GlobalTheory.Ex.NumB
theorem _root_.solution (a : ℕ) (x : B.A) :
    cubN B.θ a 1 x⁻¹ x⁻¹ * B.θ x x⁻¹ x ^ a * (B.σ x * B.σ (x ^ a)) =
      cubN B.θ a 1 x x * B.θ x⁻¹ x x⁻¹ ^ a * B.σ (x ^ a * x) := by
  induction a with
  | zero => simp [cubN, B.σ_one]
  | succ a ih =>
    have s := B.σ_cub (x ^ a) x x
    have t := B.σ_cub x x x⁻¹
    have u := B.σ_inv x
    rw [inv_inv, mul_inv_cancel, mul_inv_cancel_right, B.σ_one, B.cub.s12 x⁻¹, B.cub.s12 x] at t
    rw [CubeBalance.cubN_succ, CubeBalance.cubN_succ, inv_pow, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have s := E s; have t := E t; have u := E u
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_one] at ih s t u ⊢
    linear_combination (norm := module) ih + s - t - u
end GlobalTheory.Ex.NumB
