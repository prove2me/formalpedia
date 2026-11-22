-- Prove2me | solution 1 for GridHam.accA_swap_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:31:09.990942+00:00
-- url     : https://prove2.me/submissions/c2793948-cf21-4963-acc0-c7ea72a23984

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
theorem _root_.solution : ∀ w ∈ List.range 4, ∀ h ∈ List.range 4, ∀ sx ∈ List.range w,
    ∀ sy ∈ List.range h, ∀ tx ∈ List.range w, ∀ ty ∈ List.range h,
    (AccA w h sx sy tx ty ↔ AccA w h tx ty sx sy) := by
  decide +kernel
end GridHam
