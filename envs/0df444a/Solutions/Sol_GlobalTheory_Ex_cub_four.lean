-- Prove2me | solution 1 for GlobalTheory.Ex.cub_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:32:26.001257+00:00
-- url     : https://prove2.me/submissions/2e2dea39-fd16-484b-9ca0-e164b886bc4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws

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
theorem _root_.solution (h : IsCub θ) (p q r s z : A) :
    θ (p * q) (r * s) z * θ p q z * θ r s z = θ (p * r) (q * s) z * θ p r z * θ q s z := by
  have a := h.coc (p * q) r s z
  have b := h.coc (p * r) q s z
  have c := h.coc q p r z
  rw [mul_right_comm p r q] at b
  rw [mul_comm q p, h.s01 q p, h.s01 q (p * r)] at c
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a b c ⊢
  linear_combination (norm := abel) b - a + c
end GlobalTheory.Ex
