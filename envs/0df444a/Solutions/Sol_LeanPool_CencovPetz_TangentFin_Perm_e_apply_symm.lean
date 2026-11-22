-- Prove2me | solution 1 for LeanPool.CencovPetz.TangentFin.Perm.e_apply_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:03.141535+00:00
-- url     : https://prove2.me/submissions/6cd383fc-4771-4831-bfcd-48bfe824f933

module
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariantBilinForm
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_coe
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_self
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_tangentPushforward_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.Simplex.uniform_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply
attribute [local simp] LeanPool.CencovPetz.tangentPushforward_apply


attribute [local simp] LeanPool.CencovPetz.TangentFin.Basis.dij_coe
attribute [local simp] LeanPool.CencovPetz.TangentFin.Basis.dij_self

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {n : ℕ}
open LeanPool.CencovPetz.TangentFin
open LeanPool.CencovPetz.TangentFin.Perm
open _root_.LeanPool.CencovPetz.TangentFin.Basis
namespace LeanPool.CencovPetz.TangentFin.Perm
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (i k : Fin n) :
    e (n := n) i (σ.symm k) = e (n := n) (σ i) k := by
  classical
  by_cases hk : k = σ i
  · subst hk
    have this : σ.symm (σ i) = i := by simp
    rw [this]
    simp [e, Pi.single_eq_same]
  · have hki : σ.symm k ≠ i := by
      intro h
      apply hk
      simpa using congrArg σ h
    simp [e, hk, hki]
end LeanPool.CencovPetz.TangentFin.Perm
