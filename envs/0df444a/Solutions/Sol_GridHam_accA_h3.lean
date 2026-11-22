-- Prove2me | solution 1 for GridHam.accA_h3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:41:25.684489+00:00
-- url     : https://prove2.me/submissions/2173579b-81f6-424e-968f-e66e39f06a61

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
theorem _root_.solution (w sx sy tx ty : ℕ) (hw : 4 ≤ w) :
    AccA w 3 sx sy tx ty ↔
      CCA w 3 sx sy tx ty ∧ ¬ G3 w sx tx sy ((sx + sy) % 2) ((tx + ty) % 2) := by
  rw [accA_eq]
  unfold ForbA F3A
  constructor
  · rintro ⟨hc, hf⟩
    exact ⟨hc, fun g => hf (Or.inr (Or.inr ⟨by omega, by omega, Or.inr rfl, Or.inr ⟨by omega, g⟩⟩))⟩
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    rintro (⟨hn, _⟩ | ⟨_, hn, _⟩ | ⟨_, _, _, h3⟩)
    · omega
    · omega
    · rcases h3 with ⟨hw3, _⟩ | ⟨_, g⟩
      · omega
      · exact hf g
end GridHam
