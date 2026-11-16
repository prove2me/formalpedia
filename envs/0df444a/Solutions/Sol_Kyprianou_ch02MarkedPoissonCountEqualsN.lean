-- Prove2me | solution 1 for Kyprianou.ch02MarkedPoissonCountEqualsN
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:26:17.253574+00:00
-- url     : https://prove2.me/submissions/53e6fa0d-03f0-4a88-9db8-6c700341a890

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFzero : F {0} = 0)
    (N : ℝ≥0 → Ω → ℕ)
    (T : ℕ → Ω → ℝ≥0)
    (ξ : ℕ → Ω → ℝ)
    (hNlevy : ProbabilityTheory.IsLevyProcess
       (fun t ω => (N t ω : ℝ)) P)
    (hNlaw : ∀ t : ℝ≥0,
       P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (harrival : ∀ᵐ ω ∂P,
       ∀ (n : ℕ), 0 < n →
         ∀ (t : ℝ≥0), (n ≤ N t ω ↔ T n ω ≤ t))
    (hmarklaw : ∀ k : ℕ, P.map (ξ k) = F)
    (hIID : ProbabilityTheory.iIndepFun ξ P)
    (hcross : ProbabilityTheory.Indep
      (⨆ k : ℕ, MeasurableSpace.comap (ξ k) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (N t) inferInstance) P) :
    let μ : Ω → Measure (ℝ × ℝ) := fun ω =>
      Measure.sum (fun n : ℕ =>
        Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω))
    let intensity : Measure (ℝ × ℝ) :=
      (volume.restrict (Set.Ici (0 : ℝ))).prod ((rate : ENNReal) • F)
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
       μ ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) = (N t ω : ENNReal)) := by
  have hNzero : ∀ ω : Ω, N 0 ω = 0 := by
    intro ω
    have hz : (N 0 ω : ℝ) = 0 :=
      congrFun hNlevy.start_zero ω
    exact_mod_cast hz
  filter_upwards [harrival] with ω hω
  intro t
  have hA : MeasurableSet
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  change (Measure.sum (fun n : ℕ =>
      Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω)))
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) = (N t ω : ENNReal)
  rw [Measure.sum_apply _ hA]
  have harrivalPositive (n : ℕ) : 0 < T (n + 1) ω := by
    have hnot : ¬ T (n + 1) ω ≤ 0 := by
      intro h
      have hn := (hω (n + 1) (Nat.succ_pos n) 0).2 h
      simp [hNzero] at hn
    exact lt_of_not_ge hnot
  have hmem (n : ℕ) :
      (((T (n + 1) ω : ℝ), ξ (n + 1) ω) ∈
        Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) ↔
      n < N t ω := by
    constructor
    · intro h
      have hleR : (T (n + 1) ω : ℝ) ≤ (t : ℝ) := by
        exact (Set.mem_prod.mp h).1.2
      have hle : T (n + 1) ω ≤ t := by exact_mod_cast hleR
      exact Nat.lt_of_succ_le
        ((hω (n + 1) (Nat.succ_pos n) t).2 hle)
    · intro hn
      have hle : T (n + 1) ω ≤ t :=
        (hω (n + 1) (Nat.succ_pos n) t).1
          (Nat.succ_le_of_lt hn)
      have hposR : (0 : ℝ) < (T (n + 1) ω : ℝ) := by
        exact_mod_cast harrivalPositive n
      have hleR : (T (n + 1) ω : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast hle
      simp only [Set.mem_prod, Set.mem_Ioc,
        Set.mem_univ, and_true]
      exact ⟨hposR, hleR⟩
  have hterm (n : ℕ) :
      (Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω))
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) =
        if n < N t ω then (1 : ENNReal) else 0 := by
    rw [Measure.dirac_apply' _ hA]
    by_cases hn : n < N t ω
    · have hm := (hmem n).2 hn
      simp [Set.indicator_of_mem hm, hn]
    · have hm : ¬
          (((T (n + 1) ω : ℝ), ξ (n + 1) ω) ∈
            Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) :=
        mt (hmem n).1 hn
      simp [Set.indicator_of_notMem hm, hn]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range (N t ω)) (by
    intro n hn
    simp [Finset.mem_range] at hn ⊢
    omega)]
  simp
  all_goals
    simpa only [Finset.filter_true_of_mem
      (fun i hi => Finset.mem_range.mp hi), Finset.card_range]

