-- Prove2me | solution 1 for LeanPool.CencovPetz.TangentFin.Bilin.B_dij_dij_eq_zero_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:14.475389+00:00
-- url     : https://prove2.me/submissions/5969e716-945b-4252-8f2f-daa56a3c22bd

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
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_neg
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
theorem _root_.solution (i j k l : Fin n)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) k l) = 0 := by
  classical
  let σ : Equiv.Perm (Fin n) := Equiv.swap k l
  have h := B_invariant (G := G) (n := n) (σ := σ) (u := dij (n := n) i j) (v := dij (n := n) k l)
  have hu :
      (κ (n := n) σ).tangentPushforward (dij (n := n) i j) = dij (n := n) i j := by
    calc
      (κ (n := n) σ).tangentPushforward (dij (n := n) i j)
          = dij (n := n) (σ i) (σ j) := Perm.κ_tangentPushforward_dij (n := n) (σ := σ) i j
      _ = dij (n := n) i j := by
            simp [σ, Equiv.swap_apply_of_ne_of_ne hik hil, Equiv.swap_apply_of_ne_of_ne hjk hjl]
  have hv :
      (κ (n := n) σ).tangentPushforward (dij (n := n) k l) = dij (n := n) l k := by
    simpa [σ] using (Perm.κ_tangentPushforward_dij (n := n) (σ := σ) k l)
  have hEq :
      B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) l k)
        = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) k l) := by
    simpa [hu, hv] using h
  have hneg : dij (n := n) l k = -dij (n := n) k l := by
    simpa using (Basis.dij_neg (n := n) l k)
  have hEq' :
      -B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) k l)
        = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) k l) := by
    simp_all
  linarith
end LeanPool.CencovPetz.TangentFin.Bilin
