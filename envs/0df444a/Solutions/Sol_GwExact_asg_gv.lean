-- Prove2me | solution 1 for GwExact.asg_gv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:20:34.835835+00:00
-- url     : https://prove2.me/submissions/ca515779-300f-4853-9c04-6e441895831e

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {R : Nat} {col : Nat → Nat} {i c : Nat} (hc : c < R) :
    asg R col (i * R + c) = decide (col i = c) := by
  have hR : 0 < R := by omega
  have h1 : (i * R + c) / R = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right c i hR, Nat.div_eq_of_lt hc, Nat.zero_add]
  have h2 : (i * R + c) % R = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  simp only [asg, h1, h2]
end GwExact
