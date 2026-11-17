-- Prove2me | solution 2 for Kyprianou.ProofPreparation.finite_poisson_count_real_total_hasLaw
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:14:24.218795+00:00
-- url     : https://prove2.me/submissions/e2f4a7e9-2157-41bf-bf23-abff323fc050

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

theorem poisson_charfun_continuous_in_rate
    (rate : ℕ → ℝ≥0) (r : ℝ≥0)
    (hrate : Tendsto rate atTop (𝓝 r)) (t : ℝ) :
    Tendsto (fun n => charFun ((poissonMeasure (rate n)).map
      (Nat.cast : ℕ → ℝ)) t)
      atTop (𝓝 (charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) t)) := by
  simp_rw [charFun_map_cast_poissonMeasure]
  apply Tendsto.cexp
  apply Tendsto.mul_const
  have h1 : Tendsto (fun n => ((rate n : ℝ) : ℂ)) atTop (𝓝 ((r : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp ((NNReal.continuous_coe.tendsto r).comp hrate)
  simpa using h1

theorem poisson_prefix_rates_tendsto
    (rate : ℕ → ℝ≥0) (hsum : Summable rate) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, rate k)
      atTop (𝓝 ((∑' k, (rate k : ENNReal)).toNNReal)) := by
  rw [← ENNReal.coe_tsum hsum, ENNReal.toNNReal_coe]
  exact hsum.hasSum.tendsto_sum_nat

theorem poisson_prefix_distribution_to_poisson_rate
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P) (hsum : Summable rate) :
    TendstoInDistribution
      (fun n (w : Omega) =>
        (((∑ k ∈ Finset.range (n + 1), N k w) : Nat) : Real))
      atTop (Nat.cast : Nat -> Real) (fun _ => P)
      (poissonMeasure ((∑' k, (rate k : ENNReal)).toNNReal)) := by
  have hN : ∀ k, AEMeasurable (N k) P := fun k => aemeasurable_of_poisson_law P _ _ (hlaw k)
  refine ⟨fun n => measurable_from_nat.comp_aemeasurable
    (Finset.aemeasurable_fun_sum _ fun k _ => hN k), measurable_from_nat.aemeasurable, ?_⟩
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have hr : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), rate k) atTop
      (𝓝 ((∑' k, (rate k : ENNReal)).toNNReal)) :=
    (poisson_prefix_rates_tendsto rate hsum).comp (tendsto_add_atTop_nat 1)
  have h := poisson_charfun_continuous_in_rate _ _ hr t
  simp only [ProbabilityMeasure.coe_mk]
  convert h using 2 with n
  exact congrArg (fun μ => charFun μ t) (finite_prefix_real_poisson_law P rate N hlaw hind n)

theorem finite_poisson_count_real_total_hasLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P)
    (hsum : Summable rate)
    (hfinite : ∀ᵐ w ∂P,
      (∑' k, ((N k w : Nat) : ENNReal)) < ⊤) :
    P.map (fun w : Omega =>
      ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal) =
      (poissonMeasure ((∑' k, (rate k : ENNReal)).toNNReal)).map
        (Nat.cast : Nat -> Real) := by
  have hN : ∀ k, AEMeasurable (N k) P := fun k => aemeasurable_of_poisson_law P _ _ (hlaw k)
  have h2 := poisson_prefix_distribution_to_poisson_rate P rate N hlaw hind hsum
  have hZ : AEMeasurable (fun w : Omega => ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal) P :=
    ENNReal.measurable_toReal.comp_aemeasurable
      (AEMeasurable.ennreal_tsum fun k => measurable_from_nat.comp_aemeasurable (hN k))
  have h1 : TendstoInDistribution
      (fun n (w : Omega) => (((∑ k ∈ Finset.range (n + 1), N k w) : Nat) : Real))
      atTop (fun w : Omega => ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal)
      (fun _ => P) P := by
    apply tendstoInDistribution_of_ae_tendsto
      (fun n => measurable_from_nat.comp_aemeasurable
        (Finset.aemeasurable_fun_sum _ fun k _ => hN k)) hZ
    filter_upwards [hfinite] with w hw
    have h3 := ((ENNReal.tendsto_toReal hw.ne).comp
      (ENNReal.tendsto_nat_tsum (fun k => ((N k w : ℕ) : ENNReal)))).comp (tendsto_add_atTop_nat 1)
    refine h3.congr fun n => ?_
    simp only [Function.comp]
    rw [← Nat.cast_sum, ENNReal.toReal_natCast]
  exact tendstoInDistribution_unique _ h1 h2

end Kyprianou.ProofPreparation

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P)
    (hsum : Summable rate)
    (hfinite : ∀ᵐ w ∂P,
      (∑' k, ((N k w : Nat) : ENNReal)) < ⊤) :
    P.map (fun w : Omega =>
      ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal) =
      (poissonMeasure ((∑' k, (rate k : ENNReal)).toNNReal)).map
        (Nat.cast : Nat -> Real) :=
  Kyprianou.ProofPreparation.finite_poisson_count_real_total_hasLaw P rate N hlaw hind hsum hfinite
