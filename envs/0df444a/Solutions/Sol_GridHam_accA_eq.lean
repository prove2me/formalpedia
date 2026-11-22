-- Prove2me | solution 1 for GridHam.accA_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:34:58.648182+00:00
-- url     : https://prove2.me/submissions/28eb5956-3379-482a-a2f2-7d0f74f6b975

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h sx sy tx ty : ℕ) :
    AccA w h sx sy tx ty ↔ CCA w h sx sy tx ty ∧ ¬ ForbA w h sx sy tx ty := Iff.rfl
end GridHam
