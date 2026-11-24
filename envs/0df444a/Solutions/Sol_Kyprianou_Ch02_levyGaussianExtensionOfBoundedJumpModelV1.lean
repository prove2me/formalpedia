-- Prove2me | solution 1 for Kyprianou.Ch02.levyGaussianExtensionOfBoundedJumpModelV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:08:02.015285+00:00
-- url     : https://prove2.me/submissions/d7676bab-fea0-44c7-a0f0-a3b9eed580af

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Theorems.Thm_Kyprianou_Ch01_isBrownianReal_toStrictLevyProcess
import Theorems.Thm_Kyprianou_Ch01_isLevyProcess_realScale
import Theorems.Thm_Kyprianou_Ch01_charFun_scaledBrownianZeroStart
import Theorems.Thm_AvramDividend_Classical_avram_gbB135_native_centered_brownian_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB43_native_centered_brownian_path_continuous
import Theorems.Thm_Kyprianou_Ch01_independentLevyProductSum
import Theorems.Thm_Kyprianou_Ch01_charFun_independentProductProcessSum
import Theorems.Thm_Kyprianou_Ch02_levyProductContinuousAddSmallJumpMassMeanEqV1
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {A : Type} [MeasurableSpace A] (M : Measure A)
    [IsProbabilityMeasure M] (J : ℝ≥0 → A → ℝ)
    (hJ : IsLevyProcess J M) (hJm : ∀ t, Measurable (J t))
    (hJchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (M.map (J t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, 0, levyMeasure, hlevyMeasure⟩ ξ))
    (hJbound : ∀ n : ℕ,
      (∫⁻ ω : A, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |J (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => J u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |J (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => J u ω) (s : ℝ≥0)|
           else 0) ∂M) ≤
        (n : ℝ≥0∞) *
          (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂levyMeasure))
    : ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsLevyProcess X P ∧
        (∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (P.map (X t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              Kyprianou.Ch01.levyTripleExponent
                ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) ∧
        (∀ n : ℕ,
          (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) ≤
            (n : ℝ≥0∞) *
              (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂levyMeasure)) := by
  let Q : Measure (ℝ≥0 → ℝ) := gaussianLimit
  let v : ℝ≥0 := σ ^ 2
  let B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω =>
    Real.sqrt (v : ℝ) * (brownian t ω - brownian 0 ω)
  have hbase : IsLevyProcess (fun t ω => brownian t ω - brownian 0 ω) Q :=
    Kyprianou.Ch01.isBrownianReal_toStrictLevyProcess Q brownian
      ProbabilityTheory.isBrownianReal_brownian_avram
  have hB : IsLevyProcess B Q :=
    Kyprianou.Ch01.isLevyProcess_realScale Q _ (Real.sqrt (v : ℝ)) hbase
  have hBm : ∀ t, Measurable (B t) := fun t => measurable_const.mul
    (AvramDividend.Classical.avram_gbB135_native_centered_brownian_coordinate_measurable t)
  have hBcont : ∀ ω, Continuous (fun t => B t ω) := fun ω => continuous_const.mul
    (AvramDividend.Classical.avram_gbB43_native_centered_brownian_path_continuous ω)
  let X : ℝ≥0 → A × (ℝ≥0 → ℝ) → ℝ := fun t p => J t p.1 + B t p.2
  refine ⟨A × (ℝ≥0 → ℝ), inferInstance, M.prod Q, X, inferInstance,
    Kyprianou.Ch01.independentLevyProductSum M Q J B hJ hB hJm hBm, ?_, ?_⟩
  · intro t ξ
    have hchar := Kyprianou.Ch01.charFun_independentProductProcessSum
      M Q (J t) (B t) (hJm t) (hBm t) ξ
    have hCharB := Kyprianou.Ch01.charFun_scaledBrownianZeroStart
      Q brownian ProbabilityTheory.isBrownianReal_brownian_avram v t ξ
    change charFun ((M.prod Q).map (X t)) ξ = _
    rw [show charFun ((M.prod Q).map (X t)) ξ = _ from hchar, hJchar t ξ]
    change _ * charFun (Q.map (B t)) ξ = _
    rw [show charFun (Q.map (B t)) ξ = _ from hCharB]
    rw [← Complex.exp_add]
    congr 1
    dsimp [Kyprianou.Ch01.levyTripleExponent, v]
    push_cast
    ring
  · intro n
    exact (Kyprianou.Ch02.levyProductContinuousAddSmallJumpMassMeanEqV1
      M Q J B hJ hBcont (n : ℝ≥0)).trans_le (hJbound n)
