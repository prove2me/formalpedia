-- Prove2me | solution 1 for GridHam.accA_w3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:58:21.9987+00:00
-- url     : https://prove2.me/submissions/5fe9d531-73d1-4b5a-bdb4-8169db5a6798

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
theorem _root_.solution (h sx sy tx ty : ℕ) (hh : 4 ≤ h) :
    AccA 3 h sx sy tx ty ↔
      CCA 3 h sx sy tx ty ∧ ¬ G3 h sy ty sx ((sx + sy) % 2) ((tx + ty) % 2) := by
  rw [accA_eq]
  unfold ForbA F3A
  constructor
  · rintro ⟨hc, hf⟩
    exact ⟨hc, fun g => hf (Or.inr (Or.inr ⟨by omega, by omega, Or.inl rfl, Or.inl ⟨rfl, g⟩⟩))⟩
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    rintro (⟨hn, _⟩ | ⟨_, hn, _⟩ | ⟨_, _, _, h3⟩)
    · omega
    · omega
    · rcases h3 with ⟨_, g⟩ | ⟨hn, _⟩
      · exact hf g
      · exact hn rfl
end GridHam
