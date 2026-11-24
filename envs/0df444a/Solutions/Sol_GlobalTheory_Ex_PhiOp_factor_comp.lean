-- Prove2me | solution 1 for GlobalTheory.Ex.PhiOp.factor_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:13:41.761276+00:00
-- url     : https://prove2.me/submissions/512a1286-d79c-4aaa-9745-52c14211a804

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FeOfPhiTriv
import Theorems.Thm_GlobalTheory_Ex_PhiOp_cubN_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_split


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
theorem _root_.solution (k : ℕ) (a b b' x : A) :
    cubN θ k (a * b' ^ k) b x / θ (a * b' ^ k) x b * (cubN θ k a b' (x * b) / θ a (x * b) b') * θ a b b' =
      cubN θ k a (b * b') x / θ a x (b * b') * (θ a (b' ^ k) b * cubN θ k 1 b' b) := by
  have e₁ := h.N_add k a b' x b
  have e₂ := h.N_split k (a * b' ^ k) b x
  have e₃ := h.N_split k a b' x
  have e₄ := h.N_split k a (b * b') x
  have e₅ := h.N_split k a b' b
  have e₆ := cubN_mul h k b b' x
  have e₇ := h.coc a (b' ^ k) (b ^ k) x
  have e₈ := h.coc x b b' a
  have r : ∀ u v, θ u v a = θ a u v := fun u v => by rw [h.s12, h.s01]
  simp only [r] at e₈
  rw [mul_comm (b' ^ k), ← mul_pow, h.s01 (b' ^ k)] at e₇
  rw [h.s12 b' x b, h.s01 b' b x] at e₁
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅; have a₆ := E e₆
  have a₇ := E e₇; have a₈ := E e₈
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃ - a₄ + a₅ - a₆ + a₇ - a₈
end GlobalTheory.Ex.PhiOp
