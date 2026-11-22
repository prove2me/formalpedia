-- Prove2me | solution 1 for GridHam.accA_transpose_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:31:37.397066+00:00
-- url     : https://prove2.me/submissions/c681c676-316e-450f-9824-6559c871f25e

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
    (AccA w h sx sy tx ty ↔ AccA h w sy sx ty tx) := by
  decide +kernel
end GridHam
