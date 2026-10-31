-- Prove2me | solution 1 for MeanRiskBellman.Recursion.lemma_2_1_recursiveness
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:53:21.963617+00:00
-- url     : https://prove2.me/submissions/70e6dad4-417b-432d-ba4f-ebf683fbebfc

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
    TimeConsistent T ρ ↔
      ∀ t < T, ∀ X : Ω → ℝ, Measurable X → ρ t X = ρ t (fun ω => -ρ (t + 1) X ω) := by
  have := hP.isProb
  constructor
  · intro hTC t ht X hX
    have hXs : StronglyMeasurable X := hX.stronglyMeasurable
    have hR1 := hρ.risk (t + 1) ht
    have hZ : StronglyMeasurable[ℱ (t + 1)] (fun ω => -(ρ (t + 1) X ω)) :=
      (hR1.stronglyMeasurable _ (memLp_of_sm hXs)).neg
    have hZ' := hZ.mono (ℱ.le (t + 1))
    have h2 : ρ (t + 1) (fun ω => -(ρ (t + 1) X ω)) = ρ (t + 1) X := by
      have hz0 : StronglyMeasurable (0 : Ω → ℝ) := stronglyMeasurable_zero
      have htr := hR1.translation 0 _ (memLp_of_sm hz0) (memLp_of_sm hZ') hZ
      have h0 : ρ (t + 1) 0 = 0 := ae_eq_to_eq hP.pos
        ((hR1.stronglyMeasurable _ (memLp_of_sm hz0)).mono (ℱ.le _))
        hz0 hR1.map_zero
      rw [zero_add] at htr
      have htr' := ae_eq_to_eq hP.pos
        ((hR1.stronglyMeasurable _ (memLp_of_sm hZ')).mono (ℱ.le _))
        (((hR1.stronglyMeasurable _ (memLp_of_sm hz0)).mono (ℱ.le _)).sub hZ')
        htr
      rw [htr', h0]; funext ω; simp
    exact hTC t ht _ _ hX hZ'.measurable h2.symm
  · intro h t ht X Y hX hY hXY
    rw [h t ht X hX, h t ht Y hY, hXY]
