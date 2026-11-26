-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.dartSymm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:13.45247+00:00
-- url     : https://prove2.me/submissions/570b977c-1021-4188-946b-745acd9283ad

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (d : G.Dart) : dartSymm G d = d.symm := rfl
end LeanPool.K5MinorFreeChoosability
