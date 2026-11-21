-- Prove2me | solution 1 for GwExact.holds_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:02.694106+00:00
-- url     : https://prove2.me/submissions/20204fae-0245-4e7e-b7a5-f7111f95f70c

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
    (hbit : cl.p.testBit (i * R + c) = true) (heq : col i = c) : cl.Holds (asg R col) :=
  ⟨i * R + c, Or.inl ⟨hbit, by rw [asg_gv hc]; simp [heq]⟩⟩
end GwExact
