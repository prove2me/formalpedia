-- Prove2me | solution 1 for LovaszLocalLemma.lll_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:28:44.262213+00:00
-- url     : https://prove2.me/submissions/e6f8d3ae-f181-4385-b34e-d636701abb7f

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Definitions.Def_LovaszLocalLemma_Solution
public import Theorems.Thm_LocalLemma_lll_symmetric


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LovaszLocalLemma
namespace LovaszLocalLemma
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (Γ : SimpleGraph (Fin n))
    [DecidableRel Γ.Adj] (hΓ : IsDependencyGraph μ A Γ) {p : ℝ} {d : ℕ}
    (hp : ∀ i, μ.real (A i) ≤ p) (hd : ∀ i, Γ.degree i ≤ d)
    (hc : Real.exp 1 * p * (d + 1) ≤ 1) :
    0 < μ.real (⋂ i, (A i)ᶜ) :=
  LocalLemma.lll_symmetric μ A hA Γ hΓ hp hd hc
end LovaszLocalLemma
