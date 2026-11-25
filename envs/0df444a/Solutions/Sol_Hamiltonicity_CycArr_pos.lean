-- Prove2me | solution 1 for Hamiltonicity.CycArr.pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:13:39.856337+00:00
-- url     : https://prove2.me/submissions/2cdac706-f579-4755-baee-82784bfc4851

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
namespace Hamiltonicity.CycArr
theorem _root_.solution (h : CycArr G m f) : 0 < m := by have := h.three_le; omega
end Hamiltonicity.CycArr
