-- Prove2me | solution 1 for MurtySimon.ediam_le_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:27.666967+00:00
-- url     : https://prove2.me/submissions/b0bea3de-3a61-4201-b69a-f4bef8ccad0d

module
public import Mathlib
public import Definitions.Def_MurtySimon_Defs
public import Theorems.Thm_MurtySimon_diamLeTwo_iff_edist

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open SimpleGraph
variable {V : Type*}
namespace MurtySimon
theorem _root_.solution (G : SimpleGraph V) : G.ediam ≤ 2 ↔ DiamLeTwo G := by
  rw [ediam_le_iff, diamLeTwo_iff_edist]
end MurtySimon
