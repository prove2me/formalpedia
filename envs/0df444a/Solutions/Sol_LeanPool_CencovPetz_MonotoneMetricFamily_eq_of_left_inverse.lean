-- Prove2me | solution 1 for LeanPool.CencovPetz.MonotoneMetricFamily.eq_of_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:19.852556+00:00
-- url     : https://prove2.me/submissions/36cafcfc-2570-4295-b00a-8f2b47c296ac

module
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Definitions.Def_LeanPool_CencovPetz_LeftInverseIsometry
public import Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_comp_eq_of_left_inverse
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply



set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
open LeanPool.CencovPetz.MonotoneMetricFamily
namespace LeanPool.CencovPetz.MonotoneMetricFamily
theorem _root_.solution (G : MonotoneMetricFamily) {α β : Type u} [Fintype α] [Fintype β]
    (κ : MarkovMorphism α β) (κ' : MarkovMorphism β α) (p : Simplex α)
    (hp : κ'.pushforward (κ.pushforward p) = p)
    (ht : ∀ u : tangentSpace (α := α), κ'.tangentPushforward (κ.tangentPushforward u) = u)
    (u v : tangentSpace (α := α)) :
    G.g (α := β) (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward v) =
      G.g (α := α) p u v := by
  have h := comp_eq_of_left_inverse (G := G) κ κ' p hp ht
  simpa [LinearMap.BilinForm.comp_apply, MarkovMorphism.tangentPushforwardLinear_apply] using
    congrArg (fun B : LinearMap.BilinForm ℝ (tangentSpace (α := α)) => B u v) h
end LeanPool.CencovPetz.MonotoneMetricFamily
