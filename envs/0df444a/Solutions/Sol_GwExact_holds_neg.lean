-- Prove2me | solution 1 for GwExact.holds_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:22:58.965768+00:00
-- url     : https://prove2.me/submissions/fc074bd9-afc1-431e-8ee6-c15ec6799be0

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses
public import Theorems.Thm_GwExact_asg_gv

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {R : Nat} {col : Nat → Nat} {cl : Cls} {i c : Nat} (hc : c < R)
    (hbit : cl.n.testBit (i * R + c) = true) (hne : col i ≠ c) : cl.Holds (asg R col) :=
  ⟨i * R + c, Or.inr ⟨hbit, by rw [asg_gv hc]; simp [hne]⟩⟩
end GwExact
