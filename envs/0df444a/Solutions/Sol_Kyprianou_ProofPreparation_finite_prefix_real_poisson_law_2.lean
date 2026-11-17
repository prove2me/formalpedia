-- Prove2me | solution 2 for Kyprianou.ProofPreparation.finite_prefix_real_poisson_law
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:06:52.985878+00:00
-- url     : https://prove2.me/submissions/0fb08140-073b-4f1b-8c4e-d9c1b2067201

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem independent_prefix_sum_of_aemeasurable
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (N : ℕ → Ω → ℕ)
    (hind : iIndepFun N P)
    (hN : ∀ k, AEMeasurable (N k) P)
    (s : Finset ℕ) (k : ℕ) (hk : k ∉ s) :
    IndepFun (fun ω => ∑ j ∈ s, N j ω) (N k) P := by
  have := hind.indepFun_finsetSum_of_notMem₀ hN hk
  convert this using 1
  funext ω
  simp [Finset.sum_apply]
theorem aemeasurable_of_poisson_law
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (r : ℝ≥0) (N : Ω → ℕ)
    (hlaw : P.map N = poissonMeasure r) :
    AEMeasurable N P := by
  by_contra h
  rw [Measure.map_of_not_aemeasurable h] at hlaw
  have := measure_univ (μ := poissonMeasure r)
  rw [← hlaw] at this
  simp at this
theorem poisson_prefix_sum_law
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℕ → ℝ≥0) (N : ℕ → Ω → ℕ)
    (hlaw : ∀ k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P) :
    ∀ n : ℕ,
      P.map (fun ω => ∑ k ∈ Finset.range (n + 1), N k ω) =
        poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k) := by
  have hN : ∀ k, AEMeasurable (N k) P := fun k => aemeasurable_of_poisson_law P _ _ (hlaw k)
  intro n
  induction n with
  | zero => simpa using hlaw 0
  | succ n ih =>
    have hX : HasLaw (fun ω => ∑ k ∈ Finset.range (n + 1), N k ω)
        (poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k)) P :=
      ⟨Finset.aemeasurable_fun_sum _ fun k _ => hN k, ih⟩
    have hY : HasLaw (N (n+1)) (poissonMeasure (rate (n+1))) P := ⟨hN _, hlaw _⟩
    have hXY := independent_prefix_sum_of_aemeasurable P N hind hN (Finset.range (n+1)) (n+1)
      (by simp)
    have h := (IndepFun.hasLaw_add_poissonMeasure hXY hX hY).map_eq
    rw [Finset.sum_range_succ _ (n+1)]
    convert h using 2
    funext ω
    simp [Finset.sum_range_succ]
theorem finite_prefix_real_poisson_law
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P) (n : Nat) :
    P.map (fun w : Omega =>
      (((∑ k ∈ Finset.range (n + 1), N k w) : Nat) : Real)) =
      (poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k)).map
        (Nat.cast : Nat -> Real) := by
  have hN : ∀ k, AEMeasurable (N k) P := fun k => aemeasurable_of_poisson_law P _ _ (hlaw k)
  rw [← poisson_prefix_sum_law P rate N hlaw hind n,
    AEMeasurable.map_map_of_aemeasurable measurable_from_nat.aemeasurable
      (Finset.aemeasurable_fun_sum _ fun k _ => hN k)]
  rfl

end Kyprianou.ProofPreparation

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P) (n : Nat) :
    P.map (fun w : Omega =>
      (((∑ k ∈ Finset.range (n + 1), N k w) : Nat) : Real)) =
      (poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k)).map
        (Nat.cast : Nat -> Real) := by
  first
  | exact Kyprianou.ProofPreparation.finite_prefix_real_poisson_law
  | exact Kyprianou.ProofPreparation.finite_prefix_real_poisson_law ..
  | (apply Kyprianou.ProofPreparation.finite_prefix_real_poisson_law <;> assumption)
