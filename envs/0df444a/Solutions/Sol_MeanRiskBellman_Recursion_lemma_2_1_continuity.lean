-- Prove2me | solution 1 for MeanRiskBellman.Recursion.lemma_2_1_continuity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:53:22.662983+00:00
-- url     : https://prove2.me/submissions/29cc2387-d4b3-46c5-a55b-cc1f4b53215d

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_DynamicRisk

open MeasureTheory

set_option linter.unusedSectionVars false

namespace MRBL21Aux

open MeanRiskBellman.Recursion

variable {Ω : Type*} [Fintype Ω] [mΩ : MeasurableSpace Ω]

lemma ae_eq_to_eq {P : Measure Ω} (hpos : ∀ A : Set Ω, MeasurableSet A → A.Nonempty → 0 < P A)
    {f g : Ω → ℝ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) (h : f =ᵐ[P] g) :
    f = g := by
  funext ω
  by_contra hne
  have hs : MeasurableSet {ω | ¬ f ω = g ω} :=
    (measurableSet_eq_fun hf.measurable hg.measurable).compl
  have hp := hpos _ hs ⟨ω, hne⟩
  rw [Filter.EventuallyEq, ae_iff] at h
  exact (ne_of_gt hp) h

lemma ae_le_to_le {P : Measure Ω} (hpos : ∀ A : Set Ω, MeasurableSet A → A.Nonempty → 0 < P A)
    {f g : Ω → ℝ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) (h : f ≤ᵐ[P] g) :
    f ≤ g := by
  intro ω
  by_contra hne
  have hs : MeasurableSet {ω | ¬ f ω ≤ g ω} := by
    simp only [not_le]
    exact measurableSet_lt hg.measurable hf.measurable
  have hp := hpos _ hs ⟨ω, hne⟩
  rw [Filter.EventuallyLE, ae_iff] at h
  exact (ne_of_gt hp) h

lemma memLp_of_sm {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → ℝ} (hf : StronglyMeasurable f) :
    MemLp f ⊤ P :=
  MemLp.of_bound hf.aestronglyMeasurable (∑ ω, ‖f ω‖)
    (ae_of_all _ fun ω => Finset.single_le_sum (f := fun ω => ‖f ω‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ ω))

end MRBL21Aux

open MeanRiskBellman.Recursion MRBL21Aux in
theorem solution {Ω : Type*} [Fintype Ω] [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (T : ℕ) (ℱ : Filtration ℕ mΩ) (ρ : ℕ → (Ω → ℝ) → Ω → ℝ)
    (hP : IsFinFilteredSpace P T ℱ) (hρ : IsDynamicConvexRiskMeasure P T ℱ ρ) :
    ∀ t ≤ T, ContinuousOn (ρ t) {X : Ω → ℝ | Measurable X} := by
  have := hP.isProb
  intro t ht
  have hR := hρ.risk t ht
  -- one-sided bound: ρ Y - dist X Y ≤ ρ X
  have key : ∀ X Y : Ω → ℝ, Measurable X → Measurable Y → ∀ ω,
      ρ t Y ω - dist X Y ≤ ρ t X ω := by
    intro X Y hX hY ω
    have hXs := hX.stronglyMeasurable
    have hYs := hY.stronglyMeasurable
    set c := dist X Y
    have hc : StronglyMeasurable[ℱ t] (fun _ : Ω => c) := stronglyMeasurable_const
    have hle : X ≤ Y + fun _ => c := by
      intro ω'
      have hd := dist_le_pi_dist X Y ω'
      rw [Real.dist_eq] at hd
      have := (abs_sub_le_iff.1 hd).1
      simp only [Pi.add_apply]; linarith
    have hm := ae_le_to_le hP.pos
      ((hR.stronglyMeasurable _ (memLp_of_sm (hYs.add stronglyMeasurable_const))).mono (ℱ.le t))
      ((hR.stronglyMeasurable _ (memLp_of_sm hXs)).mono (ℱ.le t))
      (hR.monotone _ _ (memLp_of_sm hXs) (memLp_of_sm (hYs.add stronglyMeasurable_const))
        (Filter.Eventually.of_forall hle))
    have htr := ae_eq_to_eq hP.pos
      ((hR.stronglyMeasurable _ (memLp_of_sm (hYs.add stronglyMeasurable_const))).mono (ℱ.le t))
      (((hR.stronglyMeasurable _ (memLp_of_sm hYs)).mono (ℱ.le t)).sub stronglyMeasurable_const)
      (hR.translation Y _ (memLp_of_sm hYs) (memLp_of_sm stronglyMeasurable_const) hc)
    have := hm ω
    rw [htr] at this
    simpa using this
  rw [Metric.continuousOn_iff]
  intro X hX ε hε
  refine ⟨ε, hε, fun Y hY hd => ?_⟩
  refine lt_of_le_of_lt ?_ hd
  rw [dist_pi_le_iff dist_nonneg]
  intro ω
  have a := key X Y hX hY ω
  have b := key Y X hY hX ω
  rw [dist_comm Y X] at b
  rw [Real.dist_eq, abs_sub_le_iff, dist_comm Y X]
  exact ⟨by linarith, by linarith⟩
