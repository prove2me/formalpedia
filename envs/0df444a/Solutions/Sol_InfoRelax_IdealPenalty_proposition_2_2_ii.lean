-- Prove2me | solution 1 for InfoRelax.IdealPenalty.proposition_2_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:47:52.917468+00:00
-- url     : https://prove2.me/submissions/533ed3c7-a9c6-4178-a282-9897b79b9c1d

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework
import Definitions.Def_InfoRelax_IdealPenalty_RecursiveModel
import Definitions.Def_InfoRelax_IdealPenalty_Penalty

set_option autoImplicit false
open MeasureTheory InfoRelax.IdealPenalty

theorem solution {Ω X : Type*} [mΩ : MeasurableSpace Ω] {T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (h𝔾 : IsRelaxation 𝔽 𝔾) (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ)
    (hw : GeneratingFns μ w) :
    (∀ a : Fin (T + 1) → X, Adapted 𝔾 (fun t => penaltyComp μ 𝔽 𝔾 w t a)) ∧
      ∀ (t : Fin (T + 1)) (a a' : Fin (T + 1) → X), (∀ s, s ≤ t → a s = a' s) →
        penaltyComp μ 𝔽 𝔾 w t a = penaltyComp μ 𝔽 𝔾 w t a' := by
  refine ⟨fun a t => ?_, fun t a a' h => ?_⟩
  · unfold penaltyComp
    have h1 : StronglyMeasurable[𝔾 t] (μ[w t a | 𝔾 t]) := stronglyMeasurable_condExp
    have h2 : StronglyMeasurable[𝔽 t] (μ[w t a | 𝔽 t]) := stronglyMeasurable_condExp
    exact (h1.sub (h2.mono (h𝔾 t))).measurable
  · unfold penaltyComp
    rw [hw.1 t a a' h]
