-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.MinorModel.SameBranch.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:19:20.126138+00:00
-- url     : https://prove2.me/submissions/4b3ead17-97df-4f36-8fb4-fdd7a04a26eb

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_MinorModel_eq_of_mem


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
open LeanPool.K5MinorFreeChoosability.MinorModel
variable (M : MinorModel G H)
namespace LeanPool.K5MinorFreeChoosability.MinorModel
namespace SameBranch
theorem _root_.solution {M : MinorModel G H} {u v x : V} (h : M.SameBranch u v)
    (h' : M.SameBranch v x) : M.SameBranch u x := by
  rcases h with rfl | ⟨w, hu, hv⟩
  · exact h'
  rcases h' with rfl | ⟨w', hv', hx⟩
  · exact Or.inr ⟨w, hu, hv⟩
  · obtain rfl := M.eq_of_mem hv hv'
    exact Or.inr ⟨w, hu, hx⟩
end SameBranch
end LeanPool.K5MinorFreeChoosability.MinorModel
