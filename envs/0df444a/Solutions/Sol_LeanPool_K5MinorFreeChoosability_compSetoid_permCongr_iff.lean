-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.compSetoid_permCongr_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:21.786706+00:00
-- url     : https://prove2.me/submissions/f312f40c-b06e-445c-b598-19ffb8b2c53c

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_le
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_left
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_compSetoid_right

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution {D' : Type*} (e : D ≃ D') (σ α : Perm D) (a b : D) :
    compSetoid σ α a b ↔ compSetoid (e.permCongr σ) (e.permCongr α) (e a) (e b) := by
  constructor
  · intro h
    have := compSetoid_le (Setoid.comap e (compSetoid (e.permCongr σ) (e.permCongr α)))
      (fun z => by
        rw [Setoid.comap_rel]
        have := compSetoid_left (e.permCongr σ) (e.permCongr α) (e z)
        simpa [permCongr_apply] using this)
      (fun z => by
        rw [Setoid.comap_rel]
        have := compSetoid_right (e.permCongr σ) (e.permCongr α) (e z)
        simpa [permCongr_apply] using this) h
    rwa [Setoid.comap_rel] at this
  · intro h
    have := compSetoid_le (Setoid.comap e.symm (compSetoid σ α))
      (fun z => by
        rw [Setoid.comap_rel, permCongr_apply, symm_apply_apply]
        exact compSetoid_left σ α _)
      (fun z => by
        rw [Setoid.comap_rel, permCongr_apply, symm_apply_apply]
        exact compSetoid_right σ α _) h
    rw [Setoid.comap_rel] at this
    simpa using this
end LeanPool.K5MinorFreeChoosability
