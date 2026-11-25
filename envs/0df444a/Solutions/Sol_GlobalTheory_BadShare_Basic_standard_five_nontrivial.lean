-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.standard_five_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:27:37.284385+00:00
-- url     : https://prove2.me/submissions/72abc99c-0f95-4b78-9afd-57a36fb37893

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_standard_edge_five
import Theorems.Thm_GlobalTheory_BadShare_Basic_transv_apply
import Theorems.Thm_GlobalTheory_BadShare_Basic_isUp_transv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
variable {g N}
open GlobalTheory.BadShare.Basic
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution :
    (∃ u, (levStandard g 5 true 1 2 (by norm_num)).Mem u ∧ (levStandard g 5 true 1 2 (by norm_num)).chi u ≠ 1) ∧
      ∃ u, IsUp g 5 u ∧ ¬ (levStandard g 5 true 1 2 (by norm_num)).Mem u := by
  refine ⟨⟨transv 0 3 (by decide), ⟨isUp_transv 0 3 (by decide), fun _ a b h1 h2 h3 => ?_⟩, ?_⟩,
    transv 1 3 (by decide), isUp_transv 1 3 (by decide), fun h => ?_⟩
  · simp only [levStandard, levOfChar] at h1 h2 h3
    rw [transv_apply, if_neg, if_neg, add_zero]
    · rintro ⟨rfl, rfl⟩
      simp at h1
    · rintro rfl
      omega
  · have hs : (∑ a, ∑ b, if (levStandard g 5 true 1 2 (by norm_num)).Edge a b then
        (((levStandard g 5 true 1 2 (by norm_num)).co a : (ZMod g)ˣ) : ZMod g) *
          (transv (g := g) (0 : Fin 5) 3 (by decide)).val a b else 0) = 1 := by
      simp only [standard_edge_five, transv_apply]
      simp [Fin.sum_univ_five, levStandard, levOfChar]
    unfold Lev.chi
    rw [hs]
    intro h
    exact one_ne_zero (((ZMod.isPrimitive_stdAddChar g).zmod_char_eq_one_iff g 1).1 h)
  · have := h.2 rfl 1 3 (by simp [levStandard, levOfChar]) (by simp [levStandard, levOfChar])
      (by simp [levStandard, levOfChar])
    rw [transv_apply] at this
    simp at this
end GlobalTheory.BadShare.Basic
