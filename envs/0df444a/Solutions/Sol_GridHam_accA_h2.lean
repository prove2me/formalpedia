-- Prove2me | solution 1 for GridHam.accA_h2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:41:24.8108+00:00
-- url     : https://prove2.me/submissions/76dad549-8a1e-47b6-8205-2242eaa19aa3

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
theorem _root_.solution (w sx sy tx ty : ℕ) (hw : 3 ≤ w) :
    AccA w 2 sx sy tx ty ↔ CCA w 2 sx sy tx ty ∧ ¬ F2A w 2 sx sy tx ty := by
  rw [accA_eq]
  unfold ForbA
  constructor
  · rintro ⟨hc, hf⟩
    exact ⟨hc, fun h2 => hf (Or.inr (Or.inl ⟨by omega, Or.inr rfl, h2⟩))⟩
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    rintro (⟨hn, _⟩ | ⟨_, _, h2⟩ | ⟨_, hn, _⟩)
    · omega
    · exact hf h2
    · exact hn (Or.inr rfl)
end GridHam
