-- Prove2me | solution 1 for GridHam.branchB_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:32:24.339802+00:00
-- url     : https://prove2.me/submissions/6361964b-b96f-4bb3-86bc-0966b12b2fa3

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
    AccA w h sx sy tx ty → sx ≤ 1 → w ≤ tx + 2 →
    BConcl w h sx sy tx ty (rChoice sx sy h) := by
  decide +kernel
end GridHam
