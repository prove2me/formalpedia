-- Prove2me | solution 1 for GlobalTheory.Ex.NumB.mulq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:04:30.897617+00:00
-- url     : https://prove2.me/submissions/12e71dd4-5d09-4833-9675-fa6bb687b2b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
import Theorems.Thm_GlobalTheory_Ex_mulq_succ
import Theorems.Thm_GlobalTheory_Ex_mulq_add
import Theorems.Thm_GlobalTheory_Ex_NumB_dbl_pow
import Theorems.Thm_GlobalTheory_CubeBalance_cubN_mul


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
theorem _root_.solution (a b : ℕ) (x : B.A) :
    mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) := by
  induction a with
  | zero => simp [mulq]
  | succ a ih =>
    have m := mulq_add B.cub B.σ (a * b) b x
    have c := CubeBalance.cubN_mul B.cub a b x (x ^ b)
    have d := B.dbl_pow b x
    rw [Nat.succ_mul, mulq_succ]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have m := E m; have c := E c; have d := E d
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih m c d ⊢
    linear_combination (norm := module) ih + m + c + a • d
end GlobalTheory.Ex.NumB
