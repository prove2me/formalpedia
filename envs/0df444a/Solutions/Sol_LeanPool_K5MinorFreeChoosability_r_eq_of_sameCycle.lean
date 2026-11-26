-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.r_eq_of_sameCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:23.872953+00:00
-- url     : https://prove2.me/submissions/c78f976f-24a0-4f48-b761-e48bb85c3221

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_of_step


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
variable (M : MinorModel G H) (inK : G.Dart → Prop)
variable {M inK}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {σ : Perm G.Dart} {r : V → V} (hr : ∀ z, r (σ z).fst = r z.fst)
    {a b : G.Dart} (h : SameCycle σ a b) : r a.fst = r b.fst := by
  have := sameCycle_of_step (Setoid.ker fun d : G.Dart => r d.fst)
    (fun z => by rw [Setoid.ker_def]; exact (hr z).symm) h
  rwa [Setoid.ker_def] at this
end LeanPool.K5MinorFreeChoosability
