-- Prove2me | solution 1 for HighConfRobust.fact_3_3_iii
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T10:56:28.769546+00:00
-- url     : https://prove2.me/submissions/1a9f54b2-5702-45cc-9184-37698805f635

import Mathlib
import Definitions.Def_HighConfRobust_renyiDivergence
import Theorems.Thm_HighConfRobust_fact_3_3_i

open MeasureTheory ProbabilityTheory

theorem solution {X : Type*} [MeasurableSpace X] {M : ℕ} (H : Fin M → Measure X)
    [∀ i, IsProbabilityMeasure (H i)] (p w : Fin M → ENNReal)
    (hp : ∑ i, p i = 1) (hw : ∑ i, w i = 1) (hpw : ∀ i, p i ≠ 0 → w i ≠ 0)
    (q : ℝ) (hq : 1 ≤ q) :
    HighConfRobust.renyiDivergence q (∑ i, p i • H i) (∑ i, w i • H i) ≤
      HighConfRobust.renyiDivergence q (∑ i, p i • Measure.dirac i)
        (∑ i, w i • Measure.dirac i) := by
  -- the kernel `i ↦ H i` on the discrete space `Fin M`
  let κ : Kernel (Fin M) X := ⟨fun i => H i, measurable_of_countable _⟩
  haveI : IsMarkovKernel κ := ⟨fun i => (inferInstance : IsProbabilityMeasure (H i))⟩
  have hmix : ∀ r : Fin M → ENNReal,
      κ ∘ₘ (∑ i, r i • Measure.dirac i) = ∑ i, r i • H i := by
    intro r
    ext s hs
    rw [Measure.bind_apply hs κ.aemeasurable, lintegral_finsetSum_measure,
      Measure.finsetSum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_smul_measure, lintegral_dirac]
    rfl
  have hprob : ∀ r : Fin M → ENNReal, ∑ i, r i = 1 →
      IsProbabilityMeasure (∑ i, r i • Measure.dirac i : Measure (Fin M)) := by
    intro r hr
    constructor
    rw [Measure.finsetSum_apply]
    simp [hr]
  have := hprob p hp
  have := hprob w hw
  rw [← hmix p, ← hmix w]
  exact HighConfRobust.fact_3_3_i κ _ _ q hq
