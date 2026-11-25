-- Prove2me | solution 1 for GlobalTheory.Ex.NumB.mulq_mul_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:52:56.12801+00:00
-- url     : https://prove2.me/submissions/8acdca77-eef0-4119-ac65-ad088cea3186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
import Theorems.Thm_GlobalTheory_Ex_cub_rot
import Theorems.Thm_GlobalTheory_Ex_cubN_mul_point
import Theorems.Thm_GlobalTheory_Ex_mulq_succ
import Theorems.Thm_GlobalTheory_Ex_NumB_dbl_mul
import Theorems.Thm_GlobalTheory_CubeBalance_cubN_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


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
theorem _root_.solution (a : ℕ) (x y : B.A) :
    mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y *
      (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) := by
  induction a with
  | zero => simp [mulq, cubN]
  | succ a ih =>
    have d := B.dbl_mul x y
    have f := cubN_mul_point B.cub a x y (x * y)
    have n₁ := B.cub.N_add a 1 x x y
    have n₂ := B.cub.N_add a 1 y x y
    have n₃ := B.cub.N_add a 1 x (y ^ a) y
    rw [B.cub.face, mul_one, one_mul] at n₁ n₂ n₃
    rw [cub_rot B.cub x y] at f
    rw [← cub_rot B.cub (y ^ a) y x] at n₃
    have c₁ := B.cub.compat (x ^ a) (y ^ a) x y
    have c₂ := B.cub.coc (x ^ a) (y ^ a) y x
    rw [B.cub.s12 (x ^ a * y ^ a), B.cub.s12 (x ^ a) (y ^ a * y)] at c₂
    rw [mulq_succ, mulq_succ, mulq_succ, CubeBalance.cubN_succ, CubeBalance.cubN_succ, pow_succ y]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have d := E d; have f := E f; have n₁ := E n₁; have n₂ := E n₂; have n₃ := E n₃
    have c₁ := E c₁; have c₂ := E c₂
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih d f n₁ n₂ n₃ c₁ c₂ ⊢
    linear_combination (norm := module) ih + f + n₁ + n₂ - n₃ - a • d - c₁ + c₂
end GlobalTheory.Ex.NumB
