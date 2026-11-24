-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Bridge.exists_fixed_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:51:56.196897+00:00
-- url     : https://prove2.me/submissions/b96c70c3-3f40-47cc-b006-91288afa15f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Bridge
open WithZero
namespace GlobalTheory.UnitLemma.Bridge
theorem _root_.solution {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) (π : E)
    (hπ : v π = exp (-1)) (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (hv : ∀ y, v (c y) = v y)
    (a : E) (ha : v a ≤ 1) (hd : v (a - c a) = 1) (y : E) : ∃ x, c x = x ∧ v y = v x := by
  have key : ∃ ϖ, c ϖ = ϖ ∧ v ϖ = v π := by
    by_contra h
    push Not at h
    have h1 : v (π + c π) < v π :=
      lt_of_le_of_ne (v.map_add_le le_rfl (hv π).le) (h _ (by rw [map_add, hc, add_comm]))
    have h0 : v (a * π) ≤ v π := by rw [map_mul]; exact mul_le_of_le_one_left' ha
    have h2 : v (a * π + c (a * π)) < v π :=
      lt_of_le_of_ne (v.map_add_le h0 ((hv _).le.trans h0)) (h _ (by rw [map_add, hc, add_comm]))
    have h3 : v (c a * (π + c π)) < v π := by
      rw [map_mul, hv]; exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) h1
    have h4 := v.map_sub_lt h2 h3
    rw [show a * π + c (a * π) - c a * (π + c π) = (a - c a) * π by rw [map_mul]; ring, map_mul, hd,
      one_mul] at h4
    exact lt_irrefl _ h4
  obtain ⟨ϖ, h1, h2⟩ := key
  by_cases hy : y = 0
  · exact ⟨0, map_zero _, by rw [hy]⟩
  refine ⟨ϖ ^ (-log (v y)), by rw [map_zpow₀, h1], ?_⟩
  rw [map_zpow₀, h2, hπ, ← exp_zsmul]
  simp [exp_log ((Valuation.ne_zero_iff v).2 hy)]
end GlobalTheory.UnitLemma.Bridge
