-- Prove2me | solution 1 for GlobalTheory.Ex.PhiOp.cub_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:30:12.06615+00:00
-- url     : https://prove2.me/submissions/ef0071ec-7f0a-4c44-adf7-a07153a6370c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FeOfPhiTriv

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
theorem _root_.solution (u v u' v' x : A) :
    θ (u * v) (u' * v') x * θ u' v' x * θ u v x = θ (u * u') (v * v') x * θ u u' x * θ v v' x := by
  have a := h.coc (u * v) u' v' x
  have b := h.coc v u u' x
  have c := h.coc (u * u') v v' x
  rw [mul_comm v u, h.s01 v u, h.s01 v (u * u')] at b
  rw [mul_right_comm u u' v] at c
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  have c' := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a' b' c' ⊢
  linear_combination (norm := abel) b' + c' - a'
end GlobalTheory.Ex.PhiOp
