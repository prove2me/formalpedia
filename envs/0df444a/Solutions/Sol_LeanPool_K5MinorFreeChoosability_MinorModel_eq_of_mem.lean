-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.MinorModel.eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:06.600684+00:00
-- url     : https://prove2.me/submissions/73c85d3f-1248-48f0-8d5f-c3647a8d3ad7

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {V W : Type*}
variable {G : SimpleGraph V} {k : ℕ}
open LeanPool.K5MinorFreeChoosability.MinorModel
variable {H : SimpleGraph W} (M : MinorModel G H)
namespace LeanPool.K5MinorFreeChoosability.MinorModel
theorem _root_.solution {w w' : W} {v : V} (hv : v ∈ M.branch w) (hv' : v ∈ M.branch w') :
    w = w' := by
  by_contra h
  exact Finset.disjoint_left.1 (M.branch_disjoint w w' h) hv hv'
end LeanPool.K5MinorFreeChoosability.MinorModel
