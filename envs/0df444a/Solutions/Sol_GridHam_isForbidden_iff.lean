-- Prove2me | solution 1 for GridHam.isForbidden_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:26:47.082011+00:00
-- url     : https://prove2.me/submissions/a9ee1fb9-f3c5-4212-8ce9-8ae0ea8dd0a7

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith
public import Theorems.Thm_GridHam_forbiddenCase1_iff
public import Theorems.Thm_GridHam_forbiddenCase2_iff
public import Theorems.Thm_GridHam_forbiddenCase3_iff

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h sx sy tx ty : ℕ) :
    IsForbidden w h (sx, sy) (tx, ty) ↔ ForbA w h sx sy tx ty := by
  unfold IsForbidden ForbA
  rw [← forbiddenCase1_iff, ← forbiddenCase2_iff, ← forbiddenCase3_iff]
  split_ifs with h1 h2 h3
  · constructor
    · intro hf
      exact Or.inl ⟨h1, hf⟩
    · rintro (⟨_, hf⟩ | ⟨hn, _⟩ | ⟨hn, _⟩)
      · exact hf
      · exact absurd h1 hn
      · exact absurd h1 hn
  · constructor
    · intro hf
      exact Or.inr (Or.inl ⟨h1, h2, hf⟩)
    · rintro (⟨hy, _⟩ | ⟨_, _, hf⟩ | ⟨_, hn, _⟩)
      · exact absurd hy h1
      · exact hf
      · exact absurd h2 hn
  · constructor
    · intro hf
      exact Or.inr (Or.inr ⟨h1, h2, h3, hf⟩)
    · rintro (⟨hy, _⟩ | ⟨_, hy, _⟩ | ⟨_, _, _, hf⟩)
      · exact absurd hy h1
      · exact absurd hy h2
      · exact hf
  · constructor
    · intro hf
      exact hf.elim
    · rintro (⟨hy, _⟩ | ⟨_, hy, _⟩ | ⟨_, _, hy, _⟩)
      · exact absurd hy h1
      · exact absurd hy h2
      · exact absurd hy h3
end GridHam
