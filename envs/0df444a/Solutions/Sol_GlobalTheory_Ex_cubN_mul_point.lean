-- Prove2me | solution 1 for GlobalTheory.Ex.cubN_mul_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:00:36.716802+00:00
-- url     : https://prove2.me/submissions/f942d4c4-8d68-4e24-9fee-f65019c34f77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
import Theorems.Thm_GlobalTheory_Ex_cub_four
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
theorem _root_.solution (h : IsCub θ) (a : ℕ) (x y z : A) :
    cubN θ a 1 (x * y) z * θ x y z ^ a = cubN θ a 1 x z * cubN θ a 1 y z * θ (x ^ a) (y ^ a) z := by
  induction a with
  | zero => simp [cubN, h.face]
  | succ a ih =>
    have f := cub_four h (x ^ a) (y ^ a) x y z
    simp only [CubeBalance.cubN_succ, mul_pow, pow_succ]
    replace ih := congrArg Additive.ofMul ih
    replace f := congrArg Additive.ofMul f
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at ih f ⊢
    linear_combination (norm := abel) ih + f
end GlobalTheory.Ex
