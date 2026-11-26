-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RIn.adj_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:01.976307+00:00
-- url     : https://prove2.me/submissions/5be03ea3-1fbe-4fdb-ae08-069307260ef9

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Basic
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_restrict_adj
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_refl
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_exit
attribute [local simp] LeanPool.K5MinorFreeChoosability.restrict_adj
attribute [local refl] LeanPool.K5MinorFreeChoosability.RIn.refl

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {W : Type*}
open LeanPool.K5MinorFreeChoosability.RIn
variable {G G' : SimpleGraph W} {s t : Set W} {a b c : W}
namespace LeanPool.K5MinorFreeChoosability.RIn
theorem _root_.solution (h : RIn G {a, b} a b) (hab : a ≠ b) : G.Adj a b := by
  obtain ⟨p, q, _, _, hp, hq, hqP, hpq⟩ :=
    h.exit (P := {a}) (by simp) (by simpa using hab.symm)
  simp only [Set.mem_singleton_iff] at hp hqP
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  subst hp
  rcases hq with rfl | rfl
  · exact absurd rfl hqP
  · exact hpq
end LeanPool.K5MinorFreeChoosability.RIn
