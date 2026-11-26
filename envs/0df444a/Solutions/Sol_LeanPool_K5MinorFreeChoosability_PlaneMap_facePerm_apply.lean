-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.PlaneMap.facePerm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:29.319396+00:00
-- url     : https://prove2.me/submissions/aa7d9888-f7fd-4408-8944-f06bb0697f3e

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V : Type*} (G : SimpleGraph V)
open LeanPool.K5MinorFreeChoosability.PlaneMap
variable {G} (M : PlaneMap G)
namespace LeanPool.K5MinorFreeChoosability.PlaneMap
theorem _root_.solution (d : G.Dart) : M.facePerm d = M.rot d.symm := rfl
end LeanPool.K5MinorFreeChoosability.PlaneMap
