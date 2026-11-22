-- Prove2me | solution 1 for LeanPool.CencovPetz.MonotoneMetricFamily.uniformScalar_eq_uniformScalar_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:34:59.860329+00:00
-- url     : https://prove2.me/submissions/db5cce65-930f-4fd3-97a7-afc739e90a19

module
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariantBilinForm
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Definitions.Def_LeanPool_CencovPetz_ReplicationInvariance
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarMultiple
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarConstant
public import Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_uniformScalar_eq_of_mul
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_coe
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_self
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_tangentPushforward_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.Simplex.uniform_apply
attribute [local simp] LeanPool.CencovPetz.TangentFin.Basis.dij_coe
attribute [local simp] LeanPool.CencovPetz.TangentFin.Basis.dij_self
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply
attribute [local simp] LeanPool.CencovPetz.tangentPushforward_apply



set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
open LeanPool.CencovPetz.MonotoneMetricFamily
open MarkovMorphism TangentFin
namespace LeanPool.CencovPetz.MonotoneMetricFamily
theorem _root_.solution (G : MonotoneMetricFamily) {n : ℕ} (hn : 2 ≤ n) :
    uniformScalar G n hn = uniformScalar G 2 (by decide) := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hn
  have h2n : 2 ≤ Fintype.card (Fin 2 × Fin n) := two_le_card_prod (n := 2) (m := n) (by decide) hn0
  have h2' : 2 ≤ Fintype.card (Fin n × Fin 2) := two_le_card_prod (n := n) (m := 2) hn (by decide)
  -- `c_{2*n} = c_n` via replication on `Fin n`.
  have hn_to :
      uniformScalar G (Fintype.card (Fin n × Fin 2)) h2'
        =
        uniformScalar G n hn :=
    uniformScalar_eq_of_mul (G := G) (n := n) (m := 2) hn (by decide)
  -- `c_{2*n} = c_2` via replication on `Fin 2`.
  have htwo_to :
      uniformScalar G (Fintype.card (Fin 2 × Fin n)) h2n
        =
        uniformScalar G 2 (by decide) :=
    uniformScalar_eq_of_mul (G := G) (n := 2) (m := n) (by decide) hn0
  -- Both cardinals are `2*n`.
  have hcard :
      Fintype.card (Fin n × Fin 2) = Fintype.card (Fin 2 × Fin n) := by
    simp [Nat.mul_comm]
  -- Rewrite the first equality along `hcard` and conclude.
  simp_all
end LeanPool.CencovPetz.MonotoneMetricFamily
