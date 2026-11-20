-- Prove2me | solution 1 for LevyStochCalc.Probability.measurableSet_univ_prod_window
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:19:37.147206+00:00
-- url     : https://prove2.me/submissions/70e7ed38-0d4f-42e0-bb25-267f6bc965fb

import Definitions.Def_LevyStochCalc_Probability_MarkedPredictable_F000

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Probability

universe u v w

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [MeasurableSpace E]

section Deterministic

variable {ℱ : Filtration ℝ mΩ} {ν : Measure E}

theorem _root_.solution {T : ℝ} {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) {D : Set (ℝ × E)} (hD : MeasurableSet D) :
    MeasurableSet[markedPredictableSigma ℱ ν]
      ((Set.univ : Set Ω) ×ˢ (D ∩ Set.Ioc (0 : ℝ) T ×ˢ A)) := by
  have hwin := measurableSet_univ_prod_window_self (Ω := Ω) (ν := ν) ℱ T hA hAν
  refine MeasurableSpace.induction_on_inter (C := fun D _ =>
      MeasurableSet[markedPredictableSigma ℱ ν]
        ((Set.univ : Set Ω) ×ˢ (D ∩ Set.Ioc (0 : ℝ) T ×ˢ A)))
    generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ D hD
  · have hzero : (Set.univ : Set Ω) ×ˢ ((∅ : Set (ℝ × E)) ∩ Set.Ioc (0 : ℝ) T ×ˢ A) = ∅ := by
      simp
    rw [hzero]
    exact @MeasurableSet.empty _ (markedPredictableSigma ℱ ν)
  · rintro _ ⟨S, hS, B, hB, rfl⟩
    have hset : S ×ˢ B ∩ Set.Ioc (0 : ℝ) T ×ˢ A = (S ∩ Set.Ioc (0 : ℝ) T) ×ˢ (B ∩ A) :=
      Set.prod_inter_prod
    rw [hset]
    exact measurableSet_univ_prod_timeInter (hB.inter hA)
      (ne_top_of_le_ne_top hAν (measure_mono Set.inter_subset_right)) hS
  · intro t _ iht
    have hset : (Set.univ : Set Ω) ×ˢ (tᶜ ∩ Set.Ioc (0 : ℝ) T ×ˢ A)
        = ((Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T ×ˢ A))
          \ ((Set.univ : Set Ω) ×ˢ (t ∩ Set.Ioc (0 : ℝ) T ×ˢ A)) := by
      ext p
      simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_sdiff, Set.mem_inter_iff,
        Set.mem_compl_iff, not_and]
      tauto
    rw [hset]
    exact hwin.diff iht
  · intro f _ _ ihf
    have hset : (Set.univ : Set Ω) ×ˢ ((⋃ i, f i) ∩ Set.Ioc (0 : ℝ) T ×ˢ A)
        = ⋃ i, ((Set.univ : Set Ω) ×ˢ (f i ∩ Set.Ioc (0 : ℝ) T ×ˢ A)) := by
      ext p
      simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_iUnion, Set.mem_inter_iff]
      tauto
    rw [hset]
    exact MeasurableSet.iUnion ihf

end Deterministic

end LevyStochCalc.Probability
