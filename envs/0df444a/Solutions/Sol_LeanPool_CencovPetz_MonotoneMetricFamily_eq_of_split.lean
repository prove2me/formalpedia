-- Prove2me | solution 1 for LeanPool.CencovPetz.MonotoneMetricFamily.eq_of_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:55.662482+00:00
-- url     : https://prove2.me/submissions/e189275e-9fcf-4d51-8975-0b08f32d1f03

module
public import Definitions.Def_LeanPool_CencovPetz_Splitting
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Definitions.Def_LeanPool_CencovPetz_LeftInverseIsometry
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_SplittingInvariance
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_merge_pushforward_split
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_merge_tangentPushforward_split
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_eq_of_left_inverse
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply



set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
open LeanPool.CencovPetz.MonotoneMetricFamily
namespace LeanPool.CencovPetz.MonotoneMetricFamily
theorem _root_.solution (G : MonotoneMetricFamily)
    (m : α → ℕ) (hm : ∀ a, 0 < m a) (p : Simplex α)
    (u v : tangentSpace (α := α)) :
    G.g (α := MarkovMorphism.SplitTarget (α := α) m)
        ((MarkovMorphism.split (α := α) m hm).pushforward p)
        ((MarkovMorphism.split (α := α) m hm).tangentPushforward u)
        ((MarkovMorphism.split (α := α) m hm).tangentPushforward v)
      = G.g (α := α) p u v := by
  classical
  let κ : MarkovMorphism α (MarkovMorphism.SplitTarget (α := α) m) :=
    MarkovMorphism.split (α := α) m hm
  let κ' : MarkovMorphism (MarkovMorphism.SplitTarget (α := α) m) α :=
    MarkovMorphism.merge (α := α) m hm
  refine MonotoneMetricFamily.eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_ u v
  · simpa [κ, κ'] using
      MarkovMorphism.merge_pushforward_split
        (α := α) (m := m) (hm := hm) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.merge_tangentPushforward_split
        (α := α) (m := m) (hm := hm) (u := u)
end LeanPool.CencovPetz.MonotoneMetricFamily
