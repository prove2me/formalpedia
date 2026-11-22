-- Prove2me | solution 1 for GridHam.accA_h1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:41:24.323672+00:00
-- url     : https://prove2.me/submissions/429db9a0-e07f-467e-9a84-cb811471f70c

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
theorem _root_.solution (w sx sy tx ty : ℕ) (hw : 2 ≤ w) :
    AccA w 1 sx sy tx ty ↔ CCA w 1 sx sy tx ty ∧ EndsA w sx sy tx ty := by
  rw [accA_eq]
  unfold ForbA F1A EndsA
  constructor
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    by_contra hn
    exact hf (Or.inl ⟨Or.inr rfl, Or.inr ⟨by omega, hn⟩⟩)
  · rintro ⟨hc, he⟩
    refine ⟨hc, ?_⟩
    rintro (⟨_, hf⟩ | ⟨hn, _⟩ | ⟨hn, _⟩)
    · rcases hf with ⟨hw1, _⟩ | ⟨_, hne⟩
      · omega
      · exact hne he
    · exact hn (Or.inr rfl)
    · exact hn (Or.inr rfl)
end GridHam
