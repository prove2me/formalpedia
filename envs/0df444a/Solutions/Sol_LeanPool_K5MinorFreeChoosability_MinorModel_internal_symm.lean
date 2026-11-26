-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.MinorModel.internal_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:17.078806+00:00
-- url     : https://prove2.me/submissions/3075d403-1ae0-4af4-824d-9518244f17e8

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
open LeanPool.K5MinorFreeChoosability.MinorModel
variable (M : MinorModel G H)
namespace LeanPool.K5MinorFreeChoosability.MinorModel
theorem _root_.solution {z : G.Dart} : M.Internal z.symm ↔ M.Internal z := by
  constructor <;> rintro ⟨w, h1, h2⟩ <;> exact ⟨w, h2, h1⟩
end LeanPool.K5MinorFreeChoosability.MinorModel
