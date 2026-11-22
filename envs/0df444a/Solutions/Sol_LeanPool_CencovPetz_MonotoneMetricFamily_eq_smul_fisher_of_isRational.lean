-- Prove2me | solution 1 for LeanPool.CencovPetz.MonotoneMetricFamily.eq_smul_fisher_of_isRational
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:36:57.70091+00:00
-- url     : https://prove2.me/submissions/11317caf-c026-495b-85fd-eebed8fc5acd

module
public import Definitions.Def_LeanPool_CencovPetz_RationalPoint
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarConstant
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Definitions.Def_LeanPool_CencovPetz_SplittingInvariance
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarMultiple
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_CencovSplitPoint
public import Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_eq_smul_fisher_of_isSplitRepresentable
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_IsRational_isSplitRepresentable
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
open MarkovMorphism
namespace LeanPool.CencovPetz.MonotoneMetricFamily
theorem _root_.solution (G : MonotoneMetricFamily)
    {α : Type} [Fintype α] [Nonempty α]
    (p : Simplex α) (hp : Simplex.IsRational (α := α) p)
    {a0 a1 : α} (ha01 : a0 ≠ a1) :
    ∀ u v : tangentSpace (α := α),
      G.g (α := α) p u v = (uniformScalar G 2 (by decide)) * fisherBilin p u v := by
  simpa using
    (eq_smul_fisher_of_isSplitRepresentable (G := G) (p := p) (hp := hp.isSplitRepresentable) ha01)
end LeanPool.CencovPetz.MonotoneMetricFamily
