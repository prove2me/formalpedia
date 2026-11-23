-- Prove2me | solution 1 for KernelRank.multiTotalCost_eq_borderTotalCost_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:44:57.50081+00:00
-- url     : https://prove2.me/submissions/f0d693fa-d76f-4de4-9066-472062631124

import Mathlib
import Definitions.Def_KernelRankLean_Defs
import Theorems.Thm_KernelRank_Component_multiCost_eq_borderCost_add

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) (cs : List Component) :
    multiTotalCost d cs =
      borderTotalCost d cs + (d - 2) * (cs.map fun c => c.poly.natDegree).sum := by
  induction cs with
  | nil => simp [multiTotalCost, borderTotalCost]
  | cons c cs ih =>
    change c.multiCost d + multiTotalCost d cs =
      (c.borderCost d + borderTotalCost d cs) +
        (d - 2) * (c.poly.natDegree + (cs.map fun c => c.poly.natDegree).sum)
    rw [c.multiCost_eq_borderCost_add hd, ih]
    ring
end KernelRank
