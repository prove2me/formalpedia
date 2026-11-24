-- Prove2me | solution 1 for Mader.side_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:08.751616+00:00
-- url     : https://prove2.me/submissions/3bf85d44-54fb-4538-95c9-995d3d821261

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
public import Definitions.Def_MaderLib_MaderSteps
public import Theorems.Thm_Mader_ndeg_le_card


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*} (G : SimpleGraph V)
namespace Mader
theorem _root_.solution [DecidableEq V] {S U X : Finset V} {m n k : ℕ} (hm : 4 * k * n ≤ m)
    (hdeg : ∀ v ∈ S, m < 2 * ndeg G S v * n) {x : V} (hxS : x ∈ S)
    (hnb : ∀ w ∈ S, G.Adj x w → w ∈ U ∪ X) : 2 * k < (U ∪ X).card := by
  have h1 := hdeg x hxS
  have h2 := ndeg_le_card G hnb
  have h3 : 2 * k * (2 * n) < ndeg G S x * (2 * n) := by
    calc 2 * k * (2 * n) = 4 * k * n := by ring
      _ ≤ m := hm
      _ < 2 * ndeg G S x * n := h1
      _ = ndeg G S x * (2 * n) := by ring
  have := Nat.lt_of_mul_lt_mul_right h3
  omega
end Mader
