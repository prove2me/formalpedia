-- Prove2me | solution 1 for GridHam.branchC_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:32:21.553144+00:00
-- url     : https://prove2.me/submissions/efe2c0fc-044b-4b2f-9601-4ed5f570e327

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
    AccA w h sx sy tx ty → sx ≤ 1 → tx + 2 < w →
    AccA (w - 2) h sx sy tx ty ∧ FreeCol (w - 3) h sx sy tx ty := by
  decide +kernel
end GridHam
