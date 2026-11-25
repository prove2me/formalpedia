-- Prove2me | solution 1 for GlobalTheory.Ex.NumB.dbl_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:38.341489+00:00
-- url     : https://prove2.me/submissions/8928f7eb-cd53-432a-9d26-b0660899bcfe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
import Theorems.Thm_GlobalTheory_Ex_cub_rot
import Theorems.Thm_GlobalTheory_Ex_mulq_succ
import Theorems.Thm_GlobalTheory_Ex_NumB_dbl_mul
import Theorems.Thm_GlobalTheory_CubeBalance_cubN_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add


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
    dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) =
      dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 := by
  induction a with
  | zero => simp [dbl, mulq, cubN, B.cub.face, B.σ_one]
  | succ a ih =>
    have d := B.dbl_mul (x ^ a) x
    rw [B.cub.s01 x (x ^ a), ← cub_rot B.cub (x ^ a) x] at d
    have n := B.cub.N_add a 1 x (x ^ a) x
    rw [B.cub.face, mul_one, one_mul, B.cub.s01 x (x ^ a)] at n
    rw [mulq_succ, CubeBalance.cubN_succ, CubeBalance.cubN_succ, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have d := E d; have n := E n
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih d n ⊢
    linear_combination (norm := module) ih + d + n
end GlobalTheory.Ex.NumB
