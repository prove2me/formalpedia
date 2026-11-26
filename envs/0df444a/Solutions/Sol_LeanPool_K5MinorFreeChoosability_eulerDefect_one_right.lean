-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.eulerDefect_one_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:15.03104+00:00
-- url     : https://prove2.me/submissions/eacce2fa-c93f-4e59-adf8-17aa50a79881

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_le
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_of_sameCycle_left
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_cycleCount_one
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_numClasses_congr


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution [Finite D] (σ : Perm D) : eulerDefect σ 1 = 0 := by
  have hK : numComponents σ 1 = cycleCount σ := by
    refine numClasses_congr (fun a b => ⟨fun h => ?_, compSetoid_of_sameCycle_left⟩)
    exact compSetoid_le (SameCycle.setoid σ) (fun z => ⟨1, by simp⟩)
      (fun z => SameCycle.refl _ _) h
  unfold eulerDefect
  rw [hK, mul_one, cycleCount_one]
  ring
end LeanPool.K5MinorFreeChoosability
