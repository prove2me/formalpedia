-- Prove2me | solution 1 for GridHam.accA_w2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:37.902799+00:00
-- url     : https://prove2.me/submissions/2c4df43e-7f15-4d17-8c30-ba5cae1487e6

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
theorem _root_.solution (h sx sy tx ty : ℕ) (hh : 2 ≤ h) :
    AccA 2 h sx sy tx ty ↔ CCA 2 h sx sy tx ty ∧ ¬ F2A 2 h sx sy tx ty := by
  rw [accA_eq]
  unfold ForbA
  constructor
  · rintro ⟨hc, hf⟩
    exact ⟨hc, fun h2 => hf (Or.inr (Or.inl ⟨by omega, Or.inl rfl, h2⟩))⟩
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    rintro (⟨hn, _⟩ | ⟨_, _, h2⟩ | ⟨_, hn, _⟩)
    · omega
    · exact hf h2
    · exact hn (Or.inl rfl)
end GridHam
