-- Prove2me | solution 1 for LeanPool.CencovPetz.MonotoneMetricFamily.comp_eq_of_replicate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:48.855174+00:00
-- url     : https://prove2.me/submissions/15f5df52-4c09-4ebd-82d2-53c1ec63d6a2

module
public import Definitions.Def_LeanPool_CencovPetz_Replication
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Definitions.Def_LeanPool_CencovPetz_LeftInverseIsometry
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_ReplicationInvariance
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_coarsen_pushforward_replicate
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_coarsen_tangentPushforward_replicate
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_comp_eq_of_left_inverse
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.Simplex.uniform_apply
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
theorem _root_.solution (G : MonotoneMetricFamily) (m : ℕ) (hm : 0 < m) (p : Simplex α) :
    (G.g (α := α × Fin m) ((MarkovMorphism.replicate (α := α) m hm).pushforward p)).comp
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforwardLinear)
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforwardLinear)
      = G.g (α := α) p := by
  classical
  let κ : MarkovMorphism α (α × Fin m) := MarkovMorphism.replicate (α := α) m hm
  let κ' : MarkovMorphism (α × Fin m) α := MarkovMorphism.coarsen (α := α) m hm
  refine MonotoneMetricFamily.comp_eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_
  · simpa [κ, κ'] using
      MarkovMorphism.coarsen_pushforward_replicate
        (α := α) (m := m) (hm := hm) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.coarsen_tangentPushforward_replicate
        (α := α) (m := m) (hm := hm) (u := u)
end LeanPool.CencovPetz.MonotoneMetricFamily
