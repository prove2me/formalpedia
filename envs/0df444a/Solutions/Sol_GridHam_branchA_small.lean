-- Prove2me | solution 1 for GridHam.branchA_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:31:47.689988+00:00
-- url     : https://prove2.me/submissions/fc016df4-d6fd-40ee-9aeb-3bcb6c2515ff

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction

set_option autoImplicit true
@[expose] public section
public section
open GridHam
set_option maxRecDepth 100000
namespace GridHam
theorem _root_.solution : ∀ w ∈ List.range 6, 4 ≤ w → ∀ h ∈ List.range (w + 1), NotPrime w h →
    ∀ sx ∈ List.range w, ∀ sy ∈ List.range h, ∀ tx ∈ List.range w, ∀ ty ∈ List.range h,
    ¬ (sx = tx ∧ sy = ty) → sx ≤ tx →
    AccA w h sx sy tx ty → 2 ≤ sx →
    AccA (w - 2) h (sx - 2) sy (tx - 2) ty ∧ FreeCol 2 h sx sy tx ty := by
  decide +kernel
end GridHam
