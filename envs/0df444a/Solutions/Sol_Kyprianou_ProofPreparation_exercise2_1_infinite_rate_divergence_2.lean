-- Prove2me | solution 2 for Kyprianou.ProofPreparation.exercise2_1_infinite_rate_divergence
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:15:06.707732+00:00
-- url     : https://prove2.me/submissions/7ec56283-9eb9-4857-8bb0-d7cd8720721f

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

theorem total_count_event_measure_le_prefix
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℕ → Ω → ℕ)
    (n m : ℕ) :
    P {ω | (∑' k, ((N k ω : ℕ) : ENNReal)) ≤ m} ≤
      P {ω | (∑ k ∈ Finset.range (n + 1), N k ω) ≤ m} := by
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have h1 : ((∑ k ∈ Finset.range (n + 1), N k ω : ℕ) : ENNReal) ≤ m := by
    push_cast
    exact (ENNReal.sum_le_tsum _).trans hω
  exact_mod_cast h1

theorem poisson_prefix_bounded_event_probability
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (rate : ℕ → ℝ≥0) (N : ℕ → Ω → ℕ)
    (hN : ∀ k, AEMeasurable (N k) P)
    (hpref : ∀ n,
      P.map (fun ω => ∑ k ∈ Finset.range (n + 1), N k ω) =
        poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k))
    (n m : ℕ) :
    P {ω | (∑ k ∈ Finset.range (n + 1), N k ω) ≤ m} =
      (poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k))
        (Set.Iic m) := by
  have hae : AEMeasurable (fun ω => ∑ k ∈ Finset.range (n + 1), N k ω) P :=
    Finset.aemeasurable_fun_sum _ fun k _ => hN k
  rw [← hpref n, Measure.map_apply₀ hae (measurableSet_Iic.nullMeasurableSet)]
  rfl

theorem poisson_singleton_probability_tendsto_zero
    (rate : ℕ → ℝ≥0)
    (hrate : Tendsto (fun n => (rate n : ℝ)) atTop atTop)
    (k : ℕ) :
    Tendsto (fun n => (poissonMeasure (rate n)) {k}) atTop (𝓝 0) := by
  simp_rw [poissonMeasure_singleton]
  rw [← ENNReal.ofReal_zero]
  apply ENNReal.tendsto_ofReal
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hrate
  have h2 := h.div_const (k ! : ℝ)
  rw [zero_div] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp]
  ring

theorem poisson_bounded_count_probability_tendsto_zero
    (rate : ℕ → ℝ≥0)
    (hrate : Tendsto (fun n => (rate n : ℝ)) atTop atTop)
    (k : ℕ) :
    Tendsto (fun n => (poissonMeasure (rate n)) (Set.Iic k))
      atTop (𝓝 0) := by
  have hset : (Set.Iic k : Set ℕ) = ((Finset.range (k+1) : Finset ℕ) : Set ℕ) := by
    ext j; simp [Nat.lt_succ_iff]
  simp_rw [hset, ← sum_measure_singleton]
  have : (0 : ℝ≥0∞) = ∑ j ∈ Finset.range (k+1), (0 : ℝ≥0∞) := by simp
  rw [this]
  exact tendsto_finset_sum _ fun j _ => poisson_singleton_probability_tendsto_zero rate hrate j

theorem poisson_prefix_rate_diverges
    (rate : ℕ → ℝ≥0)
    (hdiv : (∑' k, (rate k : ENNReal)) = ⊤) :
    Tendsto (fun n => ((∑ k ∈ Finset.range n, rate k) : ℝ))
      atTop atTop := by
  have hns : ¬ Summable rate := by
    intro hs
    exact (ENNReal.tsum_coe_ne_top_iff_summable.2 hs) hdiv
  have := NNReal.not_summable_iff_tendsto_nat_atTop.1 hns
  simpa [NNReal.coe_sum] using NNReal.tendsto_coe_atTop.2 this

theorem measure_null_of_upper_bounds_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (b : ℕ → ENNReal)
    (hupper : ∀ n, P A ≤ b n)
    (hzero : Tendsto b atTop (𝓝 0)) :
    P A = 0 :=
  le_antisymm (ge_of_tendsto' hzero hupper) bot_le

theorem ae_top_of_null_all_finite_bounds
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ENNReal)
    (hnull : ∀ m : ℕ, P {ω | f ω ≤ (m : ENNReal)} = 0) :
    ∀ᵐ ω ∂P, f ω = ⊤ := by
  rw [ae_iff]
  apply measure_mono_null _ (measure_iUnion_null hnull)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hω
  exact Set.mem_iUnion.2 ⟨m, hm.le⟩

theorem exercise2_1_infinite_rate_divergence
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P)
    (hdiv : (∑' k, (rate k : ENNReal)) = ⊤) :
    ∀ᵐ w ∂P, (∑' k, ((N k w : Nat) : ENNReal)) = ⊤ := by
  have hN : ∀ k, AEMeasurable (N k) P := fun k => aemeasurable_of_poisson_law P _ _ (hlaw k)
  have hpref := poisson_prefix_sum_law P rate N hlaw hind
  have hdivr : Tendsto (fun n => ((∑ k ∈ Finset.range (n + 1), rate k : ℝ≥0) : ℝ)) atTop atTop := by
    have := (poisson_prefix_rate_diverges rate hdiv).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, NNReal.coe_sum] using this
  apply ae_top_of_null_all_finite_bounds
  intro m
  apply measure_null_of_upper_bounds_tendsto_zero P _
    (fun n => (poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k)) (Set.Iic m))
  · intro n
    rw [← poisson_prefix_bounded_event_probability P rate N hN hpref n m]
    exact total_count_event_measure_le_prefix P N n m
  · exact poisson_bounded_count_probability_tendsto_zero _ hdivr m

end Kyprianou.ProofPreparation

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P)
    (hdiv : (∑' k, (rate k : ENNReal)) = ⊤) :
    ∀ᵐ w ∂P, (∑' k, ((N k w : Nat) : ENNReal)) = ⊤ :=
  Kyprianou.ProofPreparation.exercise2_1_infinite_rate_divergence P rate N hlaw hind hdiv
