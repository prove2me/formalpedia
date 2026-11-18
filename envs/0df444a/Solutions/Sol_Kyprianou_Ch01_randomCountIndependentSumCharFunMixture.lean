-- Prove2me | solution 1 for Kyprianou.Ch01.randomCountIndependentSumCharFunMixture
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:41:42.501023+00:00
-- url     : https://prove2.me/submissions/2087c87a-9944-49a6-912b-2505a6135eee

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_measurableVariableLengthSum
import Theorems.Thm_Kyprianou_Ch01_geometricIndependentCountMarksJointLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P)
    (xi : ℝ) :
    charFun (P.map (fun ω =>
      ∑ i ∈ Finset.range (N ω), increment i ω)) xi =
      ∑' n : ℕ,
        ((P {ω | N ω = n}).toReal : ℂ) *
        charFun (P.map (fun ω =>
          ∑ i ∈ Finset.range n, increment i ω)) xi := by
  let S : Ω → (ℕ → ℝ) := fun ω n => increment n ω
  let F : ℕ × (ℕ → ℝ) → ℝ := fun pair => ∑ i ∈ Finset.range pair.1, pair.2 i
  let ν : Measure (ℕ → ℝ) := P.map S
  let ρ : Measure ℕ := P.map N
  have hS : Measurable S := measurable_pi_lambda S (fun i => hIncMeas i)
  have hF : Measurable F := Kyprianou.Ch01.measurableVariableLengthSum
  have hPair : Measurable (fun ω => (N ω, S ω)) := hNmeas.prodMk hS
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hS.aemeasurable
  letI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hNmeas.aemeasurable
  have hJoint :
      P.map (fun ω => (N ω, S ω)) = ρ.prod ν := by
    simpa only [S, ρ, ν] using
      Kyprianou.Ch01.geometricIndependentCountMarksJointLaw
        P increment N hNmeas hIncMeas hIndependent
  have hLaw :
      P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω) =
      (ρ.prod ν).map F := by
    calc
      P.map (fun ω =>
          ∑ i ∈ Finset.range (N ω), increment i ω) =
        (P.map (fun ω => (N ω, S ω))).map F := by
          rw [Measure.map_map hF hPair]
          rfl
      _ = (ρ.prod ν).map F := by rw [hJoint]
  let g : ℕ × (ℕ → ℝ) → ℂ :=
    fun pair => Complex.exp ((xi : ℂ) * ((F pair : ℝ) : ℂ) * Complex.I)
  have hgmeas : Measurable g := by
    dsimp [g]; fun_prop
  have hg : Integrable g (ρ.prod ν) := by
    refine Integrable.of_bound hgmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall ?_)
    intro pair
    dsimp [g]
    simp [Complex.norm_exp, Complex.mul_re]
  have hFubini :
      ∫ z, g z ∂(ρ.prod ν) =
      ∫ n, ∫ seq, g (n, seq) ∂ν ∂ρ :=
    integral_prod g hg
  have hcount :
      Integrable (fun n : ℕ => ∫ seq, g (n, seq) ∂ν) ρ :=
    hg.integral_prod_left
  have hsum := MeasureTheory.integral_countable hcount
  have hcharLaw :
      charFun (P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω)) xi =
      ∫ z, g z ∂(ρ.prod ν) := by
    rw [hLaw, charFun_apply_real]
    rw [MeasureTheory.integral_map hF.aemeasurable (by fun_prop)]
  calc
    charFun (P.map (fun ω =>
      ∑ i ∈ Finset.range (N ω), increment i ω)) xi =
        ∫ z, g z ∂(ρ.prod ν) := hcharLaw
    _ = ∫ n, ∫ seq, g (n, seq) ∂ν ∂ρ := hFubini
    _ = ∑' n : ℕ, ρ.real {n} •
      (∫ seq, g (n, seq) ∂ν) := hsum
    _ = ∑' n : ℕ,
        ((P {ω | N ω = n}).toReal : ℂ) *
        charFun (P.map (fun ω =>
          ∑ i ∈ Finset.range n, increment i ω)) xi := by
      apply tsum_congr
      intro n
      have hmeasFixed : Measurable
          (fun seq : ℕ → ℝ => ∑ i ∈ Finset.range n, seq i) := by
        fun_prop
      have hmeasOriginal :
          Measurable (fun ω =>
            ∑ i ∈ Finset.range n, increment i ω) := by
        fun_prop
      have hfixed :
          ∫ seq, g (n, seq) ∂ν =
          charFun (P.map (fun ω =>
            ∑ i ∈ Finset.range n, increment i ω)) xi := by
        rw [charFun_apply_real]
        rw [MeasureTheory.integral_map hmeasOriginal.aemeasurable (by fun_prop)]
        dsimp [g, F, ν]
        rw [MeasureTheory.integral_map hS.aemeasurable (by fun_prop)]
      have hprob : ρ {n} = P {ω | N ω = n} := by
        dsimp [ρ]
        rw [Measure.map_apply hNmeas (measurableSet_singleton n)]
        rfl
      rw [hfixed]
      simp only [measureReal_def, hprob, Complex.real_smul]
