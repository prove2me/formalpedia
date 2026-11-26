-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.MinorModel.connSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:24:34.664196+00:00
-- url     : https://prove2.me/submissions/56fc56f1-dcc2-4a69-b35a-3bc3edbc2cad

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_connSet_iff_induce_connected


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {V W : Type*}
variable {G : SimpleGraph V} {k : ℕ}
open LeanPool.K5MinorFreeChoosability.MinorModel
variable {H : SimpleGraph W} (M : MinorModel G H)
namespace LeanPool.K5MinorFreeChoosability.MinorModel
theorem _root_.solution (w : W) : ConnSet G ↑(M.branch w) :=
  (connSet_iff_induce_connected _ _).2 (M.branch_connected w)
end LeanPool.K5MinorFreeChoosability.MinorModel
