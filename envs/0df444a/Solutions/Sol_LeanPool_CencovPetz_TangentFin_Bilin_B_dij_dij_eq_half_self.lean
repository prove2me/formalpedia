-- Prove2me | solution 1 for LeanPool.CencovPetz.TangentFin.Bilin.B_dij_dij_eq_half_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:08.39988+00:00
-- url     : https://prove2.me/submissions/a36cd519-849a-4a2c-a800-65bfb8d1cc35

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
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_add
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Bilin_B_dij_dij_eq_neg_half_self
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
theorem _root_.solution (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i k) =
      (1 / 2 : ℝ) * B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := by
  classical
  have hdij : dij (n := n) i k = dij (n := n) i j + dij (n := n) j k := by
    simpa using (Basis.dij_add (n := n) i j k)
  -- Expand along the right argument and use the `(-1/2)` lemma.
  set a : ℝ := B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) with ha
  have hadd :
      B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i k)
        = a + B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) := by
    -- `B u (u+v) = B u u + B u v`.
    simp_all
  have hx :
      B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) = -(1 / 2 : ℝ) * a := by
    -- Apply the main `(-1/2)` lemma and rewrite `a`.
    simpa [a] using (B_dij_dij_eq_neg_half_self (G := G) (n := n) i j k hij hjk hik)
  -- Now solve `a + (-(1/2)*a) = (1/2)*a`.
  have : a + B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) = (1 / 2 : ℝ) * a := by
    linarith [hx]
  linarith [hadd, this, ha]
end LeanPool.CencovPetz.TangentFin.Bilin
