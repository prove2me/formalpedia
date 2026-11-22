-- Prove2me | solution 1 for LeanPool.CencovPetz.TangentFin.Bilin.B_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:29.539952+00:00
-- url     : https://prove2.me/submissions/4133173a-0d0a-47af-ba48-629cbc500dd6

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
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Perm_metric_uniform_invariant
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
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (u v : V n) :
    B (G := G) (n := n)
        ((κ (n := n) σ).tangentPushforward u) ((κ (n := n) σ).tangentPushforward v)
      = B (G := G) (n := n) u v := by
  simpa [B] using (Perm.metric_uniform_invariant (G := G) (σ := σ) u v)
end LeanPool.CencovPetz.TangentFin.Bilin
