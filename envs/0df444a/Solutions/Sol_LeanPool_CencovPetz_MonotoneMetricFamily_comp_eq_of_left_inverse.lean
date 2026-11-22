-- Prove2me | solution 1 for LeanPool.CencovPetz.MonotoneMetricFamily.comp_eq_of_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:38.546669+00:00
-- url     : https://prove2.me/submissions/354a3833-8993-49e2-8e50-7d39422ec5fe

module
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Definitions.Def_LeanPool_CencovPetz_LeftInverseIsometry
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
    (ht : ∀ u : tangentSpace (α := α), κ'.tangentPushforward (κ.tangentPushforward u) = u) :
    (G.g (α := β) (κ.pushforward p)).comp κ.tangentPushforwardLinear κ.tangentPushforwardLinear
      = G.g (α := α) p := by
  classical
  have hSymm₁ :
      ((G.g (α := β) (κ.pushforward p)).comp
        κ.tangentPushforwardLinear κ.tangentPushforwardLinear).IsSymm := by
    refine ⟨fun u v => ?_⟩
    simp [LinearMap.BilinForm.comp_apply, G.symm (α := β) (p := κ.pushforward p)]
  have hSymm₂ : (G.g (α := α) p).IsSymm := by
    refine ⟨fun u v => ?_⟩
    simpa using (G.symm (α := α) (p := p) u v)
  have hdiag : ∀ u : tangentSpace (α := α),
      ((G.g (α := β) (κ.pushforward p)).comp
        κ.tangentPushforwardLinear κ.tangentPushforwardLinear) u u
          = (G.g (α := α) p) u u := by
    intro u
    have h_le :
        G.g (α := β) (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward u) ≤
          G.g (α := α) p u u := by
      simpa using (G.monotone (α := α) (β := β) κ p u)
    have h_ge :
        G.g (α := α) p u u ≤
          G.g (α := β) (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward u) := by
      have h :=
        G.monotone (α := β) (β := α) κ' (κ.pushforward p) (κ.tangentPushforward u)
      -- Simplify using the left-inverse hypotheses.
      simpa [hp, ht u] using h
    have hEq :
        G.g (α := β) (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward u) =
          G.g (α := α) p u u :=
      le_antisymm h_le h_ge
    simp [LinearMap.BilinForm.comp_apply, MarkovMorphism.tangentPushforwardLinear_apply, hEq]
  exact LinearMap.BilinForm.ext_of_isSymm hSymm₁ hSymm₂ hdiag
end LeanPool.CencovPetz.MonotoneMetricFamily
