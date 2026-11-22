-- Prove2me | solution 1 for LeanPool.CencovPetz.TangentFin.Bilin.B_dij_dij_eq_of_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:13.327909+00:00
-- url     : https://prove2.me/submissions/faa92dc3-846c-450e-9f84-9b1972bf165e

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
public import Theorems.Thm_P2M_LeanPool_CencovPetz_TangentFin_Perm___tangentPushforward_dij_a3e9a546b358
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Bilin_B_invariant
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
open LeanPool.CencovPetz.TangentFin.Bilin
open _root_.LeanPool.CencovPetz.TangentFin.Basis
open Perm
variable {n : ℕ} (G : MonotoneMetricFamily) [Nonempty (Fin n)]
namespace LeanPool.CencovPetz.TangentFin.Bilin
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (i j k l : Fin n) :
    B (G := G) (n := n) (dij (n := n) (σ i) (σ j)) (dij (n := n) (σ k) (σ l))
      = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) k l) := by
  classical
  have h := B_invariant (G := G) (n := n) (σ := σ) (u := dij (n := n) i j) (v := dij (n := n) k l)
  simpa [Perm.κ_tangentPushforward_dij] using h
end LeanPool.CencovPetz.TangentFin.Bilin
