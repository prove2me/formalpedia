-- Prove2me | solution 1 for LeanPool.CencovPetz.TangentFin.Basis.dij_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:26.096834+00:00
-- url     : https://prove2.me/submissions/5f8b9bb5-526b-4382-a76c-66feef6e84ae

module
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariantBilinForm

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {n : ℕ}
open LeanPool.CencovPetz.TangentFin
open LeanPool.CencovPetz.TangentFin.Basis
namespace LeanPool.CencovPetz.TangentFin.Basis
theorem _root_.solution (i j : Fin n) (k : Fin n) :
    (dij (n := n) i j : Fin n → ℝ) k = e (n := n) i k - e (n := n) j k :=
  rfl
end LeanPool.CencovPetz.TangentFin.Basis
