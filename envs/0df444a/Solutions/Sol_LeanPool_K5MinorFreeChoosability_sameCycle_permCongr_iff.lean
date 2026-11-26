-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.sameCycle_permCongr_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:57.056104+00:00
-- url     : https://prove2.me/submissions/62aca134-76b8-4856-8ea9-14ab215aaa90

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_of_step


set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {D' : Type*} (e : D ≃ D') (π : Perm D) (a b : D) :
    SameCycle π a b ↔ SameCycle (e.permCongr π) (e a) (e b) := by
  constructor
  · intro h
    have := sameCycle_of_step (Setoid.comap e (SameCycle.setoid (e.permCongr π)))
      (fun z => by
        rw [Setoid.comap_rel]
        change SameCycle _ _ _
        have : (e.permCongr π) (e z) = e (π z) := by simp [permCongr_apply]
        rw [← this]
        exact ⟨1, by simp⟩) h
    rwa [Setoid.comap_rel] at this
  · intro h
    have := sameCycle_of_step (Setoid.comap e.symm (SameCycle.setoid π))
      (fun z => by
        rw [Setoid.comap_rel]
        change SameCycle _ _ _
        rw [permCongr_apply, symm_apply_apply]
        exact ⟨1, by simp⟩) h
    rw [Setoid.comap_rel, symm_apply_apply, symm_apply_apply] at this
    exact this
end LeanPool.K5MinorFreeChoosability
