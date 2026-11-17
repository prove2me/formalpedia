-- Prove2me | solution 1 for Kyprianou.Ch01.levyProcess_exists_positiveGaussianTargeted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:14:49.974323+00:00
-- url     : https://prove2.me/submissions/e8c6a273-840c-4ef8-b495-3ddb1d793b0d

import Mathlib
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Theorems.Thm_Kyprianou_Ch01_isBrownianReal_toStrictLevyProcess
import Theorems.Thm_Kyprianou_Ch01_isLevyProcess_realScale
import Theorems.Thm_Kyprianou_Ch01_charFun_scaledBrownianZeroStart
import Theorems.Thm_AvramDividend_Classical_canonical_drifted_brownian_measurable
import Theorems.Thm_Kyprianou_Ch01_isLevyProcess_lift_productFst
import Theorems.Thm_Kyprianou_Ch01_isLevyProcess_lift_productSnd
import Theorems.Thm_Kyprianou_Ch01_independentLevySum
import Theorems.Thm_Kyprianou_Ch01_levyProcess_exists_zeroGaussianTargeted
import Theorems.Thm_Kyprianou_Ch01_charFun_independentProductProcessSum
import Theorems.Thm_Kyprianou_Ch01_levyTripleExponent_expGaussianFactorisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.exists_scaledBrownianGenuineLevy (v : ℝ≥0) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsLevyProcess B P ∧ (∀ t, Measurable (B t)) ∧
        ∀ (t : ℝ≥0) (xi : ℝ),
          charFun (P.map (B t)) xi =
            Complex.exp (-(((v : ℝ) * (t : ℝ) : ℂ) * (xi : ℂ) ^ 2 / 2)) := by
  classical
  let P : Measure (ℝ≥0 → ℝ) := gaussianLimit
  let B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
    fun t ω => Real.sqrt (v : ℝ) * (brownian t ω - brownian 0 ω)
  refine ⟨ℝ≥0 → ℝ, inferInstance, P, B, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · have hbase : IsLevyProcess (fun t ω => brownian t ω - brownian 0 ω) P :=
      Kyprianou.Ch01.isBrownianReal_toStrictLevyProcess
        P brownian ProbabilityTheory.isBrownianReal_brownian_avram
    exact Kyprianou.Ch01.isLevyProcess_realScale P
      (fun t ω => brownian t ω - brownian 0 ω) (Real.sqrt (v : ℝ)) hbase
  · intro t
    have hm := AvramDividend.Classical.canonical_drifted_brownian_measurable t
    have hm' : Measurable (fun ω : ℝ≥0 → ℝ =>
        brownian t ω - brownian 0 ω) := by
      have hplus := hm.add
        (measurable_const : Measurable (fun _ : ℝ≥0 → ℝ => (t : ℝ)))
      have hfun : ((fun ω : ℝ≥0 → ℝ => brownian t ω - brownian 0 ω - (t : ℝ)) +
          (fun _ : ℝ≥0 → ℝ => (t : ℝ))) =
          (fun ω : ℝ≥0 → ℝ => brownian t ω - brownian 0 ω) := by
        funext omega; dsimp; ring
      rw [hfun] at hplus
      exact hplus
    exact measurable_const.mul hm'
  · intro t xi
    exact Kyprianou.Ch01.charFun_scaledBrownianZeroStart P brownian
      ProbabilityTheory.isBrownianReal_brownian_avram v t xi

theorem Kyprianou.Ch01.independentLevyProductSum
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hXm : ∀ t, Measurable (X t))
    (hYm : ∀ t, Measurable (Y t)) :
    IsLevyProcess
      (fun t (p : Ω × Λ) => X t p.1 + Y t p.2) (P.prod Q) := by
  have hl : IsLevyProcess (fun t (p : Ω × Λ) => X t p.1) (P.prod Q) :=
    Kyprianou.Ch01.isLevyProcess_lift_productFst P Q X hX hXm
  have hr : IsLevyProcess (fun t (p : Ω × Λ) => Y t p.2) (P.prod Q) :=
    Kyprianou.Ch01.isLevyProcess_lift_productSnd P Q Y hY hYm
  have hpathX : Measurable (fun ω : Ω => fun t : ℝ≥0 => X t ω) := measurable_pi_lambda _ hXm
  have hpathY : Measurable (fun ω : Λ => fun t : ℝ≥0 => Y t ω) := measurable_pi_lambda _ hYm
  have hindep : IndepFun (fun p : Ω × Λ => fun t : ℝ≥0 => X t p.1)
      (fun p : Ω × Λ => fun t : ℝ≥0 => Y t p.2) (P.prod Q) :=
    ProbabilityTheory.indepFun_prod hpathX hpathY
  exact Kyprianou.Ch01.independentLevySum (P.prod Q)
    (fun t (p : Ω × Λ) => X t p.1)
    (fun t (p : Ω × Λ) => Y t p.2) hl hr hindep

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hpositive : 0 < T.gaussianVariance) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure μ ∧ IsLevyProcess X μ ∧
        (∀ t, Measurable (X t)) ∧
        ∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (μ.map (X t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) * Kyprianou.Ch01.levyTripleExponent T ξ) := by
  classical
  let Tzero : ProbabilityTheory.LevyKhintchineTriple :=
    ⟨T.drift, 0, T.levyMeasure, T.levyMeasure_isLevyMeasure⟩
  have hzero : Tzero.gaussianVariance = 0 := rfl
  obtain ⟨Ω, mΩ, P, X, hP, hX, hXm, hCharX⟩ :=
    Kyprianou.Ch01.levyProcess_exists_zeroGaussianTargeted Tzero hzero
  obtain ⟨Λ, mΛ, Q, Y, hQ, hY, hYm, hCharY⟩ :=
    Kyprianou.Ch01.exists_scaledBrownianGenuineLevy T.gaussianVariance
  letI : MeasurableSpace Ω := mΩ
  letI : MeasurableSpace Λ := mΛ
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure Q := hQ
  let Z : ℝ≥0 → Ω × Λ → ℝ := fun t p => X t p.1 + Y t p.2
  refine ⟨Ω × Λ, inferInstance, P.prod Q, Z, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact Kyprianou.Ch01.independentLevyProductSum P Q X Y hX hY hXm hYm
  · intro t
    exact ((hXm t).comp measurable_fst).add ((hYm t).comp measurable_snd)
  · intro t xi
    have hchar := Kyprianou.Ch01.charFun_independentProductProcessSum P Q
      (X t) (Y t) (hXm t) (hYm t) xi
    have hfactor :=
    (Kyprianou.Ch01.levyTripleExponent_expGaussianFactorisation T t xi).symm
    calc
      charFun ((P.prod Q).map (Z t)) xi =
        charFun (P.map (X t)) xi * charFun (Q.map (Y t)) xi := hchar
      _ = Complex.exp (((t : ℝ) : ℂ) * levyTripleExponent T xi) := by
        rw [hCharX t xi, hCharY t xi]
        convert hfactor using 1
        congr 1 <;> push_cast <;> ring

