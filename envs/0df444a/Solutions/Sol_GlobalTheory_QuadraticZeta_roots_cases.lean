-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.roots_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:51:36.240561+00:00
-- url     : https://prove2.me/submissions/99a22013-7953-4e88-9e8e-a53147908521

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (t n : ℤ) {p : ℕ} (hp : p.Prime) :
    (kroneckerAt (t ^ 2 - 4 * n) p = -1 ∧ ∀ β : ZMod p, β ^ 2 ≠ t * β - n) ∨
    ∃ β β' : ZMod p, β + β' = t ∧ β * β' = n ∧
      ((kroneckerAt (t ^ 2 - 4 * n) p = 0 ∧ β = β') ∨
        (kroneckerAt (t ^ 2 - 4 * n) p = 1 ∧ β ≠ β')) := by
  rcases eq_or_ne p 2 with rfl | h2
  · simp only [kroneckerAt, if_true]
    have key : ∀ t n : ZMod 8,
        (ZMod.χ₈ (t ^ 2 - 4 * n) = -1 ∧ ∀ β : ZMod 2, β ^ 2 ≠ t.cast * β - n.cast) ∨
        ∃ β β' : ZMod 2, β + β' = t.cast ∧ β * β' = n.cast ∧
          ((ZMod.χ₈ (t ^ 2 - 4 * n) = 0 ∧ β = β') ∨ (ZMod.χ₈ (t ^ 2 - 4 * n) = 1 ∧ β ≠ β')) := by
      decide
    have := key t n
    rw [ZMod.cast_intCast (by norm_num), ZMod.cast_intCast (by norm_num)] at this
    push_cast
    exact this
  · haveI := Fact.mk hp
    have h2' : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    simp only [kroneckerAt, if_neg h2, ← jacobiSym.legendreSym.to_jacobiSym]
    by_cases hs : IsSquare ((t ^ 2 - 4 * n : ℤ) : ZMod p)
    · obtain ⟨r, hr⟩ := hs
      refine Or.inr ⟨(t + r) / 2, (t - r) / 2, by field_simp; ring, ?_, ?_⟩
      · push_cast at hr
        field_simp
        linear_combination hr
      · by_cases h0 : r = 0
        · exact Or.inl ⟨(legendreSym.eq_zero_iff _ _).2 (by simp [hr, h0]), by simp [h0]⟩
        · refine Or.inr ⟨(legendreSym.eq_one_iff _ (by simp [hr, h0])).2 ⟨r, hr⟩, fun h => h0 ?_⟩
          field_simp at h
          exact mul_left_cancel₀ h2' (by linear_combination h)
    · refine Or.inl ⟨(legendreSym.eq_neg_one_iff _).2 hs, fun β h => hs ⟨2 * β - t, ?_⟩⟩
      push_cast
      linear_combination (-4) * h
end GlobalTheory.QuadraticZeta
