-- Prove2me | solution 1 for LeanPool.CencovPetz.TangentFin.Bilin.B_dij_dij_eq_neg_half_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:13.815172+00:00
-- url     : https://prove2.me/submissions/bc851942-3de6-442d-b86b-91a68485d619

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
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_add
public import Theorems.Thm_P2M_LeanPool_CencovPetz_TangentFin_Perm___tangentPushforward_dij_a3e9a546b358
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Bilin_B_symm
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
theorem _root_.solution (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) =
      -(1 / 2 : ℝ) * B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := by
  classical
  have hsymm :
      B (G := G) (n := n) (dij (n := n) j k) (dij (n := n) i j)
        = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) := by
    simpa using (B_symm (G := G) (n := n) (dij (n := n) j k) (dij (n := n) i j))
  have hself_ik :
      B (G := G) (n := n) (dij (n := n) i k) (dij (n := n) i k)
        = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := by
    have h :=
      B_invariant (G := G) (n := n) (σ := Equiv.swap j k)
        (u := dij (n := n) i j) (v := dij (n := n) i j)
    simpa [Perm.κ_tangentPushforward_dij, Equiv.swap_apply_of_ne_of_ne hij hik] using h
  have hself_jk :
      B (G := G) (n := n) (dij (n := n) j k) (dij (n := n) j k)
        = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := by
    have h :=
      B_invariant (G := G) (n := n) (σ := Equiv.swap i k)
        (u := dij (n := n) j k) (v := dij (n := n) j k)
    have hj :
        (κ (n := n) (Equiv.swap i k)).tangentPushforward (dij (n := n) j k) = dij (n := n) j i := by
      calc
        (κ (n := n) (Equiv.swap i k)).tangentPushforward (dij (n := n) j k)
            = dij (n := n) ((Equiv.swap i k) j) ((Equiv.swap i k) k) :=
              Perm.κ_tangentPushforward_dij (n := n) (σ := Equiv.swap i k) j k
        _ = dij (n := n) j i := by
              simp [Equiv.swap_apply_of_ne_of_ne hij.symm hjk]
    -- Use `dij j i = - dij i j`.
    have hj' : dij (n := n) j i = -dij (n := n) i j := by
      simpa using (Basis.dij_neg (n := n) j i)
    -- `B (-u) (-u) = B u u` for a bilinear form.
    simp_all
  -- Use `dij i k = dij i j + dij j k` and expand `B (u+v) (u+v)`.
  have hdij : dij (n := n) i k = dij (n := n) i j + dij (n := n) j k := by
    simpa using (Basis.dij_add (n := n) i j k)
  have h_expand :
      B (G := G) (n := n) (dij (n := n) i k) (dij (n := n) i k) =
        (B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j)
            + B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k))
          + (B (G := G) (n := n) (dij (n := n) j k) (dij (n := n) i j)
            + B (G := G) (n := n) (dij (n := n) j k) (dij (n := n) j k)) := by
    -- Bilinearity: expand in the left and right argument once.
    simp_all
  -- Combine invariance + symmetry to solve for the cross term.
  have hEq :
      B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j)
        =
          B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j)
          + 2 * B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k)
          + B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := by
    -- Start from `B(dij i k, dij i k) = B(dij i j, dij i j)` and expand.
    have h0 : B (G := G) (n := n) (dij (n := n) i k) (dij (n := n) i k)
        = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) := hself_ik
    -- Put everything in a shape where `linarith` can read it.
    have hsymm' :
        B (G := G) (n := n) (dij (n := n) j k) (dij (n := n) i j)
          = B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) := by
      simpa using hsymm
    -- Rewrite `B(dij j k, dij j k)` as `B(dij i j, dij i j)` and use the expansion.
    -- Then conclude.
    linarith [h0, h_expand, hself_jk, hsymm']
  set a : ℝ := B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) i j) with ha
  set x : ℝ := B (G := G) (n := n) (dij (n := n) i j) (dij (n := n) j k) with hx
  have hEq' : a = a + 2 * x + a := by simpa [a, x] using hEq
  have hx' : x = -(1 / 2 : ℝ) * a := by linarith [hEq']
  simpa [a, x] using hx'
end LeanPool.CencovPetz.TangentFin.Bilin
