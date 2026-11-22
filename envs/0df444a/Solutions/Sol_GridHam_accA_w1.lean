-- Prove2me | solution 1 for GridHam.accA_w1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:58:21.075944+00:00
-- url     : https://prove2.me/submissions/1446ae13-85dc-4b85-ba56-61f615f15e79

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
public import Theorems.Thm_GridHam_accA_eq

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (h sx sy tx ty : ℕ) (_hh : 2 ≤ h) :
    AccA 1 h sx sy tx ty ↔ CCA 1 h sx sy tx ty ∧ EndsV h sx sy tx ty := by
  rw [accA_eq]
  unfold ForbA F1A EndsV
  constructor
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    by_contra hn
    exact hf (Or.inl ⟨Or.inl rfl, Or.inl ⟨rfl, hn⟩⟩)
  · rintro ⟨hc, he⟩
    refine ⟨hc, ?_⟩
    rintro (⟨_, hf⟩ | ⟨hn, _⟩ | ⟨hn, _⟩)
    · rcases hf with ⟨_, hne⟩ | ⟨h1, _⟩
      · exact hne he
      · exact h1 rfl
    · exact hn (Or.inl rfl)
    · exact hn (Or.inl rfl)
end GridHam
