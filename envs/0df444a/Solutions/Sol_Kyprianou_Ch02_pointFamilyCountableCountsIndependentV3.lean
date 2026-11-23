-- Prove2me | solution 1 for Kyprianou.Ch02.pointFamilyCountableCountsIndependentV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:43:33.545067+00:00
-- url     : https://prove2.me/submissions/3c98d944-7c5d-4788-a85e-e32d7a58c5fc

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_Ch02_pointFamilyCountableFiniteIntensityIndependentV3
import Theorems.Thm_Kyprianou_Ch02_pointFamilyInfiniteCountTopV3

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    ∀ {ι : Type} [Countable ι] (A : ι → Set E),
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       ProbabilityTheory.iIndepFun
         (fun i (ω : Ω) => ProbabilityTheory.poissonRandomMeasure K Y ω (A i)) P := by
  classical
  intro ι inst A hA hdis
  let B : ι → Set E := fun i =>
    if m (A i) < ⊤ then A i else ∅
  have hB : ∀ i, MeasurableSet (B i) := by
    intro i
    by_cases hi : m (A i) < ⊤
    · simpa [B, hi] using hA i
    · simp [B, hi]
  have hBfin : ∀ i, m (B i) < ⊤ := by
    intro i
    by_cases hi : m (A i) < ⊤
    · simpa [B, hi] using hi
    · simp [B, hi]
  have hBdis : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    by_cases hi : m (A i) < ⊤
    · by_cases hj : m (A j) < ⊤
      · simpa [B, hi, hj] using hdis hij
      · simp [B, hi, hj]
    · simp [B, hi]
  have hind := Kyprianou.Ch02.pointFamilyCountableFiniteIntensityIndependentV3
    P m K Y hd B hB hBfin hBdis
  let g : ι → ENNReal → ENNReal := fun i x =>
    if m (A i) < ⊤ then x else ⊤
  have hg : ∀ i, Measurable (g i) := by
    intro i
    by_cases hi : m (A i) < ⊤
    · simp only [g, if_pos hi]
      exact measurable_id
    · simp [g, hi]
  have hind' : iIndepFun (fun i (ω : Ω) =>
      g i (ProbabilityTheory.poissonRandomMeasure K Y ω (B i))) P := by
    simpa only [Function.comp_def] using hind.comp g hg
  have heq (i : ι) :
      (fun ω : Ω => g i (ProbabilityTheory.poissonRandomMeasure K Y ω (B i))) =ᵐ[P]
      (fun ω : Ω => ProbabilityTheory.poissonRandomMeasure K Y ω (A i)) := by
    by_cases hi : m (A i) < ⊤
    · filter_upwards [] with ω
      simp [g, B, hi]
    · have htop : m (A i) = ⊤ := by
        by_contra hn
        exact hi (lt_top_iff_ne_top.mpr hn)
      filter_upwards [Kyprianou.Ch02.pointFamilyInfiniteCountTopV3
          P m K Y hd (A i) (hA i) htop] with ω hw
      simp [g, B, hi, hw]
  exact (iIndepFun_congr heq).1 hind'
