-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.cycleCount_permCongr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:19:41.17211+00:00
-- url     : https://prove2.me/submissions/eae75c23-4a2c-4813-99db-8045f316a43f

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_permCongr_iff
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_congr_equiv


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {D' : Type*} (e : D ≃ D') (π : Perm D) :
    cycleCount (e.permCongr π) = cycleCount π :=
  (numClasses_congr_equiv e (sameCycle_permCongr_iff e π)).symm
end LeanPool.K5MinorFreeChoosability
