-- Prove2me | solution 1 for LovaszLocalLemma.lll
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:27:36.478442+00:00
-- url     : https://prove2.me/submissions/81ac31f6-a7a1-402b-a41f-32db86a0ff3e

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Definitions.Def_LovaszLocalLemma_Solution
public import Theorems.Thm_LocalLemma_lll


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LovaszLocalLemma
namespace LovaszLocalLemma
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (Γ : SimpleGraph (Fin n))
    [DecidableRel Γ.Adj] (hΓ : IsDependencyGraph μ A Γ) (x : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1)
    (hP : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ Γ.neighborFinset i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ μ.real (⋂ i, (A i)ᶜ) :=
  LocalLemma.lll μ A hA Γ hΓ x hx0 hx1 hP
end LovaszLocalLemma
