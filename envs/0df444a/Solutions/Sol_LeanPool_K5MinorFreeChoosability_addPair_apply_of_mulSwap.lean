-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.addPair_apply_of_mulSwap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:31.075168+00:00
-- url     : https://prove2.me/submissions/0d914f5c-61ea-4e94-bea2-ef4a93154c3e

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Hypermap

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {D : Type*}
variable [DecidableEq D]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (s : Setoid D) (π : Perm D) (x y : D)
    (h : ∀ z, s z ((π * swap x y) z)) (z : D) : addPairSetoid s x y z (π z) := by
  by_cases hzx : z = x
  · subst hzx
    refine Or.inr (Or.inl ⟨s.refl _, ?_⟩)
    simpa using h y
  by_cases hzy : z = y
  · subst hzy
    refine Or.inr (Or.inr ⟨s.refl _, ?_⟩)
    simpa using h x
  · refine Or.inl ?_
    simpa [swap_apply_of_ne_of_ne hzx hzy] using h z
end LeanPool.K5MinorFreeChoosability
