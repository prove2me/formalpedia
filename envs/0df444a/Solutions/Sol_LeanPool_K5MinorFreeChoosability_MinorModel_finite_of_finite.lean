-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.MinorModel.finite_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:11.890795+00:00
-- url     : https://prove2.me/submissions/008ace5e-344d-45f6-8aca-e259384271cc

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Reach
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_MinorModel_eq_of_mem
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_restrict_adj
attribute [local simp] LeanPool.K5MinorFreeChoosability.restrict_adj



set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
variable {V W : Type*}
variable {G : SimpleGraph V} {k : ℕ}
open LeanPool.K5MinorFreeChoosability.MinorModel
variable {H : SimpleGraph W} (M : MinorModel G H)
include M
namespace LeanPool.K5MinorFreeChoosability.MinorModel
theorem _root_.solution [Finite V] : Finite W := by
  classical
  refine Finite.of_injective (fun w => (M.branch_nonempty w).choose) (fun w w' h => ?_)
  have h1 := (M.branch_nonempty w).choose_spec
  have h2 := (M.branch_nonempty w').choose_spec
  simp only at h
  rw [h] at h1
  exact M.eq_of_mem h1 h2
end LeanPool.K5MinorFreeChoosability.MinorModel
