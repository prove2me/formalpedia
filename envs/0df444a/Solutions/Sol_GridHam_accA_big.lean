-- Prove2me | solution 1 for GridHam.accA_big
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:40:09.095657+00:00
-- url     : https://prove2.me/submissions/4bcb3e31-b3db-4c6e-90fc-662b5851b4b1

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
theorem _root_.solution (w h sx sy tx ty : ℕ) (hw : 4 ≤ w) (hh : 4 ≤ h) :
    AccA w h sx sy tx ty ↔ CCA w h sx sy tx ty := by
  rw [accA_eq]
  have hf : ¬ ForbA w h sx sy tx ty := by
    unfold ForbA
    rintro (⟨hc, _⟩ | ⟨_, hc, _⟩ | ⟨_, _, hc, _⟩) <;> omega
  exact ⟨fun H => H.1, fun hc => ⟨hc, hf⟩⟩
end GridHam
