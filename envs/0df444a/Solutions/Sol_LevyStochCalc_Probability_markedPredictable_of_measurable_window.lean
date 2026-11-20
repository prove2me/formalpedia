-- Prove2me | solution 1 for LevyStochCalc.Probability.markedPredictable_of_measurable_window
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:21:02.635439+00:00
-- url     : https://prove2.me/submissions/2a57c39a-bfa9-4f39-8b86-96e1e85b2d10

import Definitions.Def_LevyStochCalc_Probability_MarkedPredictable_F000

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Probability

universe u v w

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [MeasurableSpace E]

section Deterministic

variable {ℱ : Filtration ℝ mΩ} {ν : Measure E}

theorem AuxW.window {T : ℝ} {A : Set E} (hA : MeasurableSet A)
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

theorem _root_.solution {T : ℝ} {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) {f : ℝ × E → ℝ} (hf : Measurable f)
    (hsupp : ∀ p : ℝ × E, p ∉ Set.Ioc (0 : ℝ) T ×ˢ A → f p = 0) :
    MarkedPredictable ℱ ν fun (_ : Ω) (s : ℝ) (e : E) => f (s, e) := by
  have key : ∀ U : Set ℝ, MeasurableSet U → (0 : ℝ) ∉ U →
      MeasurableSet[markedPredictableSigma ℱ ν]
        ((fun p : Ω × ℝ × E => f (p.2.1, p.2.2)) ⁻¹' U) := by
    intro U hU h0
    have hset : (fun p : Ω × ℝ × E => f (p.2.1, p.2.2)) ⁻¹' U
        = (Set.univ : Set Ω) ×ˢ (f ⁻¹' U ∩ Set.Ioc (0 : ℝ) T ×ˢ A) := by
      ext ⟨ω, s, e⟩
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and, Set.mem_inter_iff]
      constructor
      · intro h
        refine ⟨h, ?_⟩
        by_contra hn
        have := hsupp (s, e) (by simpa [Set.mem_prod] using hn)
        rw [this] at h
        exact h0 h
      · exact fun h => h.1
    rw [hset]
    exact AuxW.window hA hAν (hf hU)
  intro U hU
  by_cases h0 : (0 : ℝ) ∈ U
  · have hc := key Uᶜ hU.compl (fun h => h h0)
    have := hc.compl
    simpa [Set.preimage_compl] using this
  · exact key U hU h0

end Deterministic

end LevyStochCalc.Probability
