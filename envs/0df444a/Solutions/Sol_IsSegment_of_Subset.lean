-- Prove2me | solution 1 for IsSegment_of_Subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:45:41.622943+00:00
-- url     : https://prove2.me/submissions/eaf9cb10-8383-4ee0-bee9-3366f4fe5004

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α]
theorem _root_.solution (D U S : Set α) (hDU : D ⊆ U) (hSU : S ⊑ U)
    (sub : S ⊆ D) : S ⊑ D := by
  exact ⟨sub, fun x hx y hy hxy => hSU.right x (hDU hx) y hy hxy⟩
