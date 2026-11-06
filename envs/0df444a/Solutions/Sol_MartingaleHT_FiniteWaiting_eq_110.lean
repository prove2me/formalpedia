-- Prove2me | solution 1 for MartingaleHT.FiniteWaiting.eq_110
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:42:01.172344+00:00
-- url     : https://prove2.me/submissions/a9ba77f7-edda-4e38-8fdb-e48a827b1c8b

import Mathlib
import Definitions.Def_ErlangA_Diffusion_SDE

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open ErlangA.Diffusion

/-- Two pre-Brownian motions have the same law on path space `ℝ≥0 → ℝ`. -/
lemma eq110_preBM_identDistrib {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
    (hX : IsPreBrownianReal X P) (hY : IsPreBrownianReal Y P')
    (hXm : ∀ t, Measurable (X t)) (hYm : ∀ t, Measurable (Y t)) :
    IdentDistrib (fun ω t => X t ω) (fun ω t => Y t ω) P P' := by
  have mX : AEMeasurable (fun ω t => X t ω) P :=
    (measurable_pi_lambda _ hXm).aemeasurable
  have mY : AEMeasurable (fun ω t => Y t ω) P' :=
    (measurable_pi_lambda _ hYm).aemeasurable
  refine ⟨mX, mY, ?_⟩
  have pX : IsProjectiveLimit (P.map (fun ω t => X t ω)) BrownianReal.projectiveFamily := by
    intro I
    rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable mX]
    exact (hX.hasLaw I).map_eq
  have pY : IsProjectiveLimit (P'.map (fun ω t => Y t ω)) BrownianReal.projectiveFamily := by
    intro I
    rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable mY]
    exact (hY.hasLaw I).map_eq
  exact pX.unique pY

theorem solution (μ : ℝ) (hμ : 0 < μ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B₁ B₂ B₃ : ℝ≥0 → Ω → ℝ)
    (h₁ : IsStandardBM P B₁) (h₂ : IsStandardBM P B₂) (h₃ : IsStandardBM P B₃)
    (hind : iIndepFun (![fun ω (t : ℝ≥0) => B₁ t ω, fun ω (t : ℝ≥0) => B₂ t ω,
      fun ω (t : ℝ≥0) => B₃ t ω] : Fin 3 → Ω → ℝ≥0 → ℝ) P)
    {Ω'' : Type*} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (B : ℝ≥0 → Ω'' → ℝ) (hB : IsStandardBM P'' B) :
    IdentDistrib (fun ω (t : ℝ≥0) => B₁ (μ.toNNReal * t) ω - B₂ (μ.toNNReal * t) ω - B₃ 0 ω)
      (fun ω (t : ℝ≥0) => B₁ (μ.toNNReal * t) ω - B₂ (μ.toNNReal * t) ω - 0) P P ∧
    IdentDistrib (fun ω (t : ℝ≥0) => B₁ (μ.toNNReal * t) ω - B₂ (μ.toNNReal * t) ω - 0)
      (fun ω (t : ℝ≥0) => Real.sqrt (2 * μ) * B t ω) P P'' := by
  obtain ⟨b₁, m₁, -⟩ := h₁
  obtain ⟨b₂, m₂, -⟩ := h₂
  obtain ⟨b₃, m₃, -⟩ := h₃
  obtain ⟨b, mb, -⟩ := hB
  set μ' : ℝ≥0 := μ.toNNReal with hμ'
  have hμ'c : ((μ' : ℝ)) = μ := Real.coe_toNNReal _ hμ.le
  constructor
  · refine IdentDistrib.of_ae_eq ?_ ?_
    · exact (measurable_pi_lambda _ fun t =>
        (((m₁ _).sub (m₂ _)).sub (m₃ 0))).aemeasurable
    · filter_upwards [b₃.eval_zero_ae_eq_zero] with ω hω
      funext t
      simp [hω]
  · set c : ℝ := Real.sqrt (2 * μ) with hc
    have hcpos : 0 < c := Real.sqrt_pos.2 (by linarith)
    set W : ℝ≥0 → Ω → ℝ := fun t ω => c⁻¹ * (B₁ (μ' * t) ω - B₂ (μ' * t) ω) with hW
    -- independence of the two paths
    have hind12 : IndepFun (fun ω (t : ℝ≥0) => B₁ t ω) (fun ω (t : ℝ≥0) => B₂ t ω) P := by
      have := hind.indepFun (i := 0) (j := 1) (by decide)
      simpa using this
    have hindpt : ∀ a b' : ℝ≥0, IndepFun (B₁ a) (B₂ b') P := by
      intro a b'
      exact hind12.comp (measurable_pi_apply a) (measurable_pi_apply b')
    have L1 : ∀ a, MemLp (B₁ a) 2 P := fun a =>
      (b₁.isGaussianProcess.hasGaussianLaw_eval a).memLp_two
    have L2 : ∀ a, MemLp (B₂ a) 2 P := fun a =>
      (b₂.isGaussianProcess.hasGaussianLaw_eval a).memLp_two
    have hWB : IsPreBrownianReal W P := by
      refine IsGaussianProcess.isPreBrownianReal_of_covariance ?_ (fun t => ?_) (fun s t hst => ?_)
      · refine ⟨fun I => ?_⟩
        have g1 := (b₁.isGaussianProcess.comp_right (fun t => μ' * t)).hasGaussianLaw I
        have g2 := (b₂.isGaussianProcess.comp_right (fun t => μ' * t)).hasGaussianLaw I
        have hmI : Measurable (fun (f : ℝ≥0 → ℝ) (i : I) => f (μ' * i)) :=
          measurable_pi_lambda _ fun i => measurable_pi_apply _
        have hI : IndepFun (fun ω => I.restrict ((B₁ ∘ fun t => μ' * t) · ω))
            (fun ω => I.restrict ((B₂ ∘ fun t => μ' * t) · ω)) P :=
          hind12.comp hmI hmI
        have hj := (IndepFun.hasGaussianLaw g1 g2 hI).fun_sub
        have hj2 := hj.fun_smul c⁻¹
        have heq : (fun ω => I.restrict (W · ω)) = fun ω => c⁻¹ •
            (I.restrict ((B₁ ∘ fun t => μ' * t) · ω) - I.restrict ((B₂ ∘ fun t => μ' * t) · ω)) := by
          funext ω
          funext i
          simp [hW, Finset.restrict]
        rw [heq]
        exact hj2
      · simp only [hW]
        rw [integral_const_mul, integral_sub ((L1 _).integrable (by norm_num))
          ((L2 _).integrable (by norm_num)), b₁.integral_eval, b₂.integral_eval]
        simp
      · simp only [hW]
        rw [covariance_const_mul_left, covariance_const_mul_right,
          covariance_fun_sub_fun_sub (L1 _) (L2 _) (L1 _) (L2 _),
          (hindpt _ _).covariance_eq_zero (L1 _) (L2 _),
          ((hindpt _ _).symm).covariance_eq_zero (L2 _) (L1 _),
          b₁.covariance_eval, b₂.covariance_eval]
        have hmin : min (μ' * s) (μ' * t) = μ' * s := min_eq_left (by gcongr)
        rw [hmin]
        push_cast
        rw [hμ'c]
        have hc2 : c * c = 2 * μ := Real.mul_self_sqrt (by linarith)
        field_simp
        nlinarith [hc2]
    have hWm : ∀ t, Measurable (W t) := fun t =>
      measurable_const.mul ((m₁ _).sub (m₂ _))
    have key := (eq110_preBM_identDistrib hWB b.toIsPreBrownianReal hWm mb).comp
      (u := fun (f : ℝ≥0 → ℝ) (t : ℝ≥0) => c * f t)
      (measurable_pi_lambda _ fun t => measurable_const.mul (measurable_pi_apply t))
    convert key using 1
    · funext ω
      funext t
      simp only [Function.comp, hW]
      field_simp
      ring
    · rfl
