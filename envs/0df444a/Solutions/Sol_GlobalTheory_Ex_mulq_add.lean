-- Prove2me | solution 1 for GlobalTheory.Ex.mulq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:44:44.862232+00:00
-- url     : https://prove2.me/submissions/074354df-1e1f-402a-b913-ce5878221724

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
import Theorems.Thm_GlobalTheory_Ex_mulq_succ
import Theorems.Thm_GlobalTheory_CubeBalance_cubN_add
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
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
namespace GlobalTheory.Ex
theorem _root_.solution (h : IsCub θ) (σ : A → U) (m n : ℕ) (x : A) :
    mulq θ σ (m + n) x * dbl θ σ x ^ (m * n) =
      mulq θ σ m x * mulq θ σ n x * (cubN θ m 1 x (x ^ n) * cubN θ n 1 x x ^ m) := by
  induction m with
  | zero => simp [mulq, cubN]
  | succ m ih =>
    have c := CubeBalance.cubN_add h m n x x
    rw [h.s12] at c
    rw [Nat.add_right_comm, mulq_succ, mulq_succ, CubeBalance.cubN_succ]
    replace ih := congrArg Additive.ofMul ih
    replace c := congrArg Additive.ofMul c
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih c ⊢
    linear_combination (norm := module) ih + c
end GlobalTheory.Ex
