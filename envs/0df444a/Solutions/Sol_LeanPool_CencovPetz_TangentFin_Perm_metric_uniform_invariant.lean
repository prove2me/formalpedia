-- Prove2me | solution 1 for LeanPool.CencovPetz.TangentFin.Perm.metric_uniform_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:34.125295+00:00
-- url     : https://prove2.me/submissions/cb9202d7-7d1e-4678-9d86-23fd90d47720

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
public import Theorems.Thm_P2M_LeanPool_CencovPetz_TangentFin_Perm___pushforward_uniform_cb98e5b2dde2
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_eq_of_equiv
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
theorem _root_.solution {n : ℕ} (G : MonotoneMetricFamily) [Nonempty (Fin n)]
    (σ : Equiv.Perm (Fin n)) (u v : V n) :
    G.g (α := Fin n) (Simplex.uniform (α := Fin n))
        ((κ (n := n) σ).tangentPushforward u) ((κ (n := n) σ).tangentPushforward v)
      = G.g (α := Fin n) (Simplex.uniform (α := Fin n)) u v := by
  classical
  simpa [κ, κ_pushforward_uniform (σ := σ)] using
    (MonotoneMetricFamily.eq_of_equiv (G := G) (α := Fin n) (β := Fin n) (e := σ)
      (p := Simplex.uniform (α := Fin n)) u v)
end LeanPool.CencovPetz.TangentFin.Perm
