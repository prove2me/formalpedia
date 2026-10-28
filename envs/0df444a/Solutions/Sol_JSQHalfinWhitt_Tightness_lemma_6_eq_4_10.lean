-- Prove2me | solution 1 for JSQHalfinWhitt.Tightness.lemma_6_eq_4_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:47:54.800326+00:00
-- url     : https://prove2.me/submissions/bf9c89f2-82dd-425f-81d2-ad15adc6bb8f

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Fluid

open JSQHalfinWhitt.Tightness in
theorem solution (n : ℕ) (β : ℝ) (hn : 1 ≤ n) (hβ : 0 < β) (hβn : β < Real.sqrt n)
    (x2 : ℝ) (hx2 : 0 ≤ x2) :
    tau β n (0, x2) = 0 := by
  have h0 : HitEq β n (0, x2) 0 := by
    unfold HitEq
    simp
  have hex : ∃ η : ℝ, 0 ≤ η ∧ HitEq β n (0, x2) η := ⟨0, le_refl _, h0⟩
  have hleast : IsLeast {η : ℝ | 0 ≤ η ∧ HitEq β n (0, x2) η} 0 :=
    ⟨⟨le_refl _, h0⟩, fun η hη => hη.1⟩
  unfold tau
  rw [if_pos hex, hleast.csInf_eq]
  rfl
