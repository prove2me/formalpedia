-- Prove2me | solution 2 for Hamiltonicity.CycArr.pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:45:19.295625+00:00
-- url     : https://prove2.me/submissions/a51019a1-a076-4890-81ad-937648cf8d3a

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
