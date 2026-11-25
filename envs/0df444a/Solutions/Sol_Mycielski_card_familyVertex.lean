-- Prove2me | solution 1 for Mycielski.card_familyVertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:26:43.886429+00:00
-- url     : https://prove2.me/submissions/d1901103-8a70-4770-9132-4af00d4d6a1c

module
public import Definitions.Def_Mycielski_Coloring
public import Definitions.Def_Mycielski_Family
public import Theorems.Thm_Mycielski_card_vertex


set_option autoImplicit true
@[expose] public section
public section
open Mycielski
open SimpleGraph
namespace Mycielski
theorem _root_.solution (n : ℕ) :
    Fintype.card (FamilyVertex n) + 1 = 3 * 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    change Fintype.card (Vertex (FamilyVertex n)) + 1 = _
    rw [card_vertex, Nat.pow_succ, ← Nat.mul_assoc, ← ih]
    omega
end Mycielski
