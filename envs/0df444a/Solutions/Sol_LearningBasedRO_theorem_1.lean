-- Prove2me | solution 1 for LearningBasedRO.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:22:59.922198+00:00
-- url     : https://prove2.me/submissions/a4594937-55dc-4d89-99c4-f1edd9627a37

import Definitions.Def_LearningBasedRO_Model
import Theorems.Thm_LearningBasedRO_requirement_3
import Theorems.Thm_LearningBasedRO_lemma_1
import Theorems.Thm_LearningBasedRO_lemma_2

open MeasureTheory

open LearningBasedRO in
theorem solution {E X Ω : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (n₁ n₂ : ℕ) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn₂ : Real.log δ / Real.log (1 - ϵ) ≤ (n₂ : ℝ)) (t : (Fin n₁ → E) → E → ℝ)
    (ht : Measurable (Function.uncurry t)) (hcont : ∀ d₁, NullSingletonClass (P.map (t d₁)))
    (g : X → E → Ω) (A : Set Ω) :
    MeasurableSet {D : (Fin n₁ → E) × (Fin n₂ → E) | IsContentSet P ϵ (uncertaintySet t ϵ δ D)} ∧
      SatisfiesReq3 (splitLaw P n₁ n₂) P ϵ δ (uncertaintySet t ϵ δ) ∧
      (∀ D : (Fin n₁ → E) × (Fin n₂ → E), IsContentSet P ϵ (uncertaintySet t ϵ δ D) →
        ∀ x : X, ROFeasible g A (uncertaintySet t ϵ δ D) x → CCPFeasible P g A ϵ x) ∧
      ENNReal.ofReal (1 - δ) ≤
        splitLaw P n₁ n₂ {D | ∀ x : X, ROFeasible g A (uncertaintySet t ϵ δ D) x →
          CCPFeasible P g A ϵ x} := by
  have hreq := requirement_3 P n₁ n₂ ϵ δ hϵ0 hϵ1 hδ0 hδ1 hn₂ t ht hcont
  refine ⟨hreq.1, hreq.2.2.2, ?_, ?_⟩
  · intro D hD x hx
    exact lemma_1 P g A ϵ (uncertaintySet t ϵ δ D) hD x hx
  · exact lemma_2 P (splitLaw P n₁ n₂) g A ϵ δ (uncertaintySet t ϵ δ) hreq.2.2.2
