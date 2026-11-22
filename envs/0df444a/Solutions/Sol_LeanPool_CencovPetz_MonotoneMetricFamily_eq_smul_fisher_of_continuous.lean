-- Prove2me | solution 1 for LeanPool.CencovPetz.MonotoneMetricFamily.eq_smul_fisher_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:37:41.274848+00:00
-- url     : https://prove2.me/submissions/be0db0d2-146f-4a2a-b9cc-663f53e5640f

module
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology
public import Definitions.Def_LeanPool_CencovPetz_UniformScalarConstant
public import Definitions.Def_LeanPool_CencovPetz_CencovSplitPoint
public import Definitions.Def_LeanPool_CencovPetz_ContinuousExtension
public import Definitions.Def_LeanPool_CencovPetz_FisherContinuity
public import Definitions.Def_LeanPool_CencovPetz_RationalDensity
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.EReal.Inv
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_CencovFinite
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_eq_smul_fisher_of_isRational
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_continuous_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_dense_setOf_isRational
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_coe
public import Theorems.Thm_LeanPool_CencovPetz_TangentFin_Basis_dij_self
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_tangentPushforward_apply
public import Theorems.Thm_P2M_LeanPool_CencovPetz_eq_of_eqOn_dense__9bd0a7151849
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
namespace LeanPool.CencovPetz.MonotoneMetricFamily
theorem _root_.solution (G : MonotoneMetricFamily)
    {α : Type} [Fintype α] [Nonempty α]
    {a0 a1 : α} (ha01 : a0 ≠ a1)
    (hG : ∀ u v : tangentSpace (α := α), Continuous fun p : Simplex α => G.g (α := α) p u v) :
    ∀ (p : Simplex α) (u v : tangentSpace (α := α)),
      G.g (α := α) p u v = (uniformScalar G 2 (by decide)) * fisherBilin p u v := by
  classical
  let s : Set (Simplex α) := {p : Simplex α | Simplex.IsRational (α := α) p}
  have hs : Dense s := by
    simpa [s] using (Simplex.dense_setOf_isRational (α := α))
  let c : ℝ := uniformScalar G 2 (by decide)
  have hF : ∀ u v : tangentSpace (α := α),
      Continuous fun p : Simplex α => c * fisherBilin p u v := by
    intro u v
    exact (Simplex.continuous_fisherBilin_apply (α := α) u v).const_mul c
  have hEqOn : ∀ p ∈ s, ∀ u v : tangentSpace (α := α),
      G.g (α := α) p u v = c * fisherBilin p u v := by
    intro p hp u v
    simpa [c, s] using (eq_smul_fisher_of_isRational (G := G) (p := p) hp ha01 u v)
  simpa [c] using
    (eq_of_eqOn_dense₂ (α := α) (s := s) hs
      (f := fun p u v => G.g (α := α) p u v)
      (g := fun p u v => c * fisherBilin p u v)
      hG hF hEqOn)
end LeanPool.CencovPetz.MonotoneMetricFamily
