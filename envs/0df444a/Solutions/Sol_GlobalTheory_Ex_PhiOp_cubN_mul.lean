-- Prove2me | solution 1 for GlobalTheory.Ex.PhiOp.cubN_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:36.655989+00:00
-- url     : https://prove2.me/submissions/4936811f-8dde-499d-b33f-038ae294699f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FeOfPhiTriv
import Theorems.Thm_GlobalTheory_Ex_PhiOp_cub_four

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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.PhiOp
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h
namespace GlobalTheory.Ex.PhiOp
theorem _root_.solution (k : ℕ) (b b' x : A) :
    cubN θ k 1 (b * b') x * θ b b' x ^ k = θ (b ^ k) (b' ^ k) x * cubN θ k 1 b x * cubN θ k 1 b' x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c := cub_four h (b ^ k) (b' ^ k) b b' x
    simp only [cubN, Finset.prod_range_succ, one_mul] at ih ⊢
    rw [mul_pow b b' k, pow_succ b, pow_succ b', pow_succ (θ b b' x)]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'
end GlobalTheory.Ex.PhiOp
