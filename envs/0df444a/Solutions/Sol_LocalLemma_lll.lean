-- Prove2me | solution 1 for LocalLemma.lll
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:26:17.933663+00:00
-- url     : https://prove2.me/submissions/3bbc914e-2871-4e0d-98ce-dfd7d07a6fdc

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Theorems.Thm_LocalLemma_lll_chain
public import Theorems.Thm_LocalLemma_lll_cond

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (Γ : SimpleGraph (Fin n))
    [DecidableRel Γ.Adj] (hΓ : IsDependencyGraph μ A Γ) (x : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1)
    (hP : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ Γ.neighborFinset i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ μ.real (⋂ i, (A i)ᶜ) := by
  have h := lll_chain μ A hA x hx1 Finset.univ
    (fun T _ => lll_cond μ A hA Γ hΓ x hx0 hx1 hP T) Finset.univ subset_rfl
  simpa [avoid] using h
end LocalLemma
