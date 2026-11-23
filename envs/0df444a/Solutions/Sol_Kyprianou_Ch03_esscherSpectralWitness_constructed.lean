-- Prove2me | solution 1 for Kyprianou.Ch03.esscherSpectralWitness_constructed
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T18:37:34.849369+00:00
-- url     : https://prove2.me/submissions/d7aac52b-bdd5-4ca3-bc2e-8aceda230d02

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace EsscherSpectralWitnessAux

private lemma exp_sub_one_sub_le_half_sq_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    Real.exp u - 1 - u ≤ u ^ 2 / 2 := by
  let h : ℝ → ℝ := fun x => x ^ 2 / 2 - (Real.exp x - 1 - x)
  have hderiv : ∀ x : ℝ, HasDerivAt h (x + 1 - Real.exp x) x := fun x => by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) (2 * x ^ (2 - 1) / 2) x :=
      (hasDerivAt_pow 2 x).div_const 2
    have h2 : HasDerivAt (fun t : ℝ => Real.exp t - 1 - t) (Real.exp x - 1) x :=
      ((Real.hasDerivAt_exp x).sub_const 1).fun_sub (hasDerivAt_id x)
    have h3 : HasDerivAt h (2 * x ^ (2 - 1) / 2 - (Real.exp x - 1)) x := h1.fun_sub h2
    have heq : 2 * x ^ (2 - 1) / 2 - (Real.exp x - 1) = x + 1 - Real.exp x := by
      norm_num; ring
    rwa [heq] at h3
  have hanti : Antitone h := by
    refine antitone_of_deriv_nonpos (fun x => (hderiv x).differentiableAt) (fun x => ?_)
    rw [(hderiv x).deriv]
    linarith [Real.add_one_le_exp x]
  have hge : h 0 ≤ h u := hanti hu
  dsimp only [h] at hge
  norm_num at hge
  linarith

private lemma abs_jumpIntegrand_le {a y : ℝ} (ha : 0 ≤ a) (hy : y < 0) :
    |Real.exp (a * y) - 1 - a * y * (Ioo (-1 : ℝ) 1).indicator 1 y| ≤
      max 1 (a ^ 2 / 2) * min 1 (y ^ 2) := by
  have hay : a * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hy.le
  by_cases h1 : -1 < y
  · have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨h1, by linarith⟩
    have hy2_le : y ^ 2 ≤ 1 := by nlinarith
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one, min_eq_right hy2_le]
    have hge0 : 0 ≤ Real.exp (a * y) - 1 - a * y := by linarith [Real.add_one_le_exp (a * y)]
    rw [abs_of_nonneg hge0]
    have hle : Real.exp (a * y) - 1 - a * y ≤ (a * y) ^ 2 / 2 :=
      exp_sub_one_sub_le_half_sq_of_nonpos hay
    have hsq : (a * y) ^ 2 / 2 = (a ^ 2 / 2) * y ^ 2 := by ring
    rw [hsq] at hle
    exact hle.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg y))
  · push Not at h1
    have hnot : y ∉ Ioo (-1 : ℝ) 1 := fun h => by linarith [h.1]
    have hy2_ge : 1 ≤ y ^ 2 := by nlinarith
    rw [Set.indicator_of_notMem hnot, mul_zero, sub_zero, min_eq_left hy2_ge, mul_one]
    have hexp_le : Real.exp (a * y) ≤ 1 := Real.exp_le_one_iff.mpr hay
    have hexp_pos : 0 ≤ Real.exp (a * y) := Real.exp_nonneg _
    rw [abs_of_nonpos (by linarith)]
    have hle1 : -(Real.exp (a * y) - 1) ≤ 1 := by linarith
    exact hle1.trans (le_max_left _ _)

private lemma abs_exp_sub_one_mul_le {beta y : ℝ} (hBeta : 0 ≤ beta) (hy : y < 0) :
    |(Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y| ≤
      beta * min 1 (y ^ 2) := by
  by_cases h1 : -1 < y
  · have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨h1, by linarith⟩
    have hy2_le : y ^ 2 ≤ 1 := by nlinarith
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one, min_eq_right hy2_le]
    have hby : beta * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hBeta hy.le
    have hexp_le : Real.exp (beta * y) ≤ 1 := Real.exp_le_one_iff.mpr hby
    have hge : beta * y + 1 ≤ Real.exp (beta * y) := Real.add_one_le_exp (beta * y)
    have habs_exp : |Real.exp (beta * y) - 1| ≤ -(beta * y) := by
      rw [abs_of_nonpos (by linarith)]; linarith
    rw [abs_mul, abs_of_neg hy]
    calc |Real.exp (beta * y) - 1| * (-y)
        ≤ (-(beta * y)) * (-y) := mul_le_mul_of_nonneg_right habs_exp (by linarith)
      _ = beta * y ^ 2 := by ring
  · push Not at h1
    have hnot : y ∉ Ioo (-1 : ℝ) 1 := fun h => by linarith [h.1]
    rw [Set.indicator_of_notMem hnot, mul_zero, abs_zero]
    exact mul_nonneg hBeta (le_min zero_le_one (sq_nonneg y))

end EsscherSpectralWitnessAux

open Kyprianou.Ch03 EsscherSpectralWitnessAux

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNatural : IsCompletedNaturalFiltration P L.X F)
    (beta : Real) (hBeta : 0 <= beta)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity L.X beta (L.ψ beta) t omega)
            omega ∂P)) :
    exists (Lbeta : AvramDividend.Classical.SpectrallyNegativeLevy Q F),
      Lbeta.X = L.X ∧ Lbeta.σ = L.σ ∧ Lbeta.ν = L.ν.withDensity
        (fun x : Real => ENNReal.ofReal (Real.exp (beta * x))) ∧ Lbeta.c = L.c + beta * L.σ ^ 2 +
        (∫ x in {x : Real | abs x < 1},
          (Real.exp (beta * x) - 1) * x ∂L.ν) := by
  let _ := hNatural
  -- Step 1: Basic measurability and lintegral representation of Q on F t
  have hX_measF : ∀ {s t : NNReal}, s ≤ t → Measurable[F t] (L.X s) :=
    fun hst => L.adapted.measurable_le hst
  have hX_meas : ∀ t : NNReal, Measurable (L.X t) := fun _ => L.adapted.measurable
  have hDens_int_eq_one : ∀ t : NNReal,
      (∫ omega, esscherDensity L.X beta (L.ψ beta) t omega ∂P) = 1 := by
    intro t
    have h1 := hEsscher t Set.univ MeasurableSet.univ
    simp only [measure_univ, Set.indicator_univ] at h1
    have hpos : 0 ≤ ∫ omega, esscherDensity L.X beta (L.ψ beta) t omega ∂P :=
      integral_nonneg fun _ => Real.exp_nonneg _
    have hofReal : ENNReal.ofReal (∫ omega, esscherDensity L.X beta (L.ψ beta) t omega ∂P) =
        ENNReal.ofReal 1 := by simpa using h1.symm
    exact (ENNReal.ofReal_eq_ofReal_iff hpos zero_le_one).mp hofReal
  have hDens_integrable : ∀ t : NNReal,
      Integrable (esscherDensity L.X beta (L.ψ beta) t) P := by
    intro t
    by_contra hnot
    have h0 : (∫ omega, esscherDensity L.X beta (L.ψ beta) t omega ∂P) = 0 := integral_undef hnot
    linarith [hDens_int_eq_one t]
  let Z : NNReal → Omega → ℝ≥0∞ := fun t omega =>
    ENNReal.ofReal (esscherDensity L.X beta (L.ψ beta) t omega)
  have hZ_measF : ∀ t : NNReal, Measurable[F t] (Z t) := fun t => by
    dsimp only [Z, esscherDensity]
    have hXt : Measurable[F t] (L.X t) := hX_measF (le_refl t)
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((hXt.const_mul beta).sub measurable_const))
  have hZ_meas : ∀ t : NNReal, Measurable (Z t) := fun t =>
    (hZ_measF t).mono (F.le t) le_rfl
  have hQ_eq_lintegral : ∀ (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A →
      Q A = ∫⁻ omega, A.indicator (Z t) omega ∂P := by
    intro t A hA
    have hA_m : MeasurableSet A := F.le t A hA
    rw [hEsscher t A hA, integral_indicator hA_m,
      ofReal_integral_eq_lintegral_ofReal (hDens_integrable t).integrableOn
        (ae_of_all _ fun _ => Real.exp_nonneg _),
      ← lintegral_indicator hA_m]
  have hZ_unit : ∀ t : NNReal, (∫⁻ omega, Z t omega ∂P) = 1 := by
    intro t
    have h := hQ_eq_lintegral t Set.univ MeasurableSet.univ
    simpa [measure_univ] using h.symm
  let W : ℝ → ℝ → ℝ≥0∞ := fun d x =>
    ENNReal.ofReal (Real.exp (beta * x - L.ψ beta * d))
  have hW_meas : ∀ d : ℝ, Measurable (W d) := fun d => by
    dsimp only [W]; fun_prop
  -- Step 2: Factorized joint law of (X_t - X_s, A ∈ F_s) under Q
  have hQ_inc_inter : ∀ {s t : NNReal} (hst : s ≤ t) {B : Set ℝ} (hB : MeasurableSet B)
      {A : Set Omega} (hA : MeasurableSet[F s] A),
      Q ((fun omega => L.X t omega - L.X s omega) ⁻¹' B ∩ A) =
        (∫⁻ omega, B.indicator (W ((t : ℝ) - (s : ℝ))) (L.X t omega - L.X s omega) ∂P) * Q A := by
    intro s t hst B hB A hA
    have hinc_F : Measurable[F t] (fun omega => L.X t omega - L.X s omega) :=
      (hX_measF (le_refl t)).sub (hX_measF hst)
    have hAFt : MeasurableSet[F t] A := F.mono hst A hA
    have hinter_F : MeasurableSet[F t] ((fun omega => L.X t omega - L.X s omega) ⁻¹' B ∩ A) :=
      (hinc_F hB).inter hAFt
    rw [hQ_eq_lintegral t _ hinter_F]
    have hfac : ∀ omega,
        ((fun omega => L.X t omega - L.X s omega) ⁻¹' B ∩ A).indicator (Z t) omega =
          B.indicator (W ((t : ℝ) - (s : ℝ))) (L.X t omega - L.X s omega) *
            A.indicator (Z s) omega := by
      intro omega
      by_cases hmem : omega ∈ (fun omega => L.X t omega - L.X s omega) ⁻¹' B ∩ A
      · rcases hmem with ⟨hBmem, hAmem⟩
        have hmem' : omega ∈ (fun omega => L.X t omega - L.X s omega) ⁻¹' B ∩ A := ⟨hBmem, hAmem⟩
        have hBmem' : L.X t omega - L.X s omega ∈ B := hBmem
        rw [Set.indicator_of_mem hmem', Set.indicator_of_mem hBmem',
          Set.indicator_of_mem hAmem]
        dsimp only [Z, W, esscherDensity]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 2; ring
      · rw [Set.indicator_of_notMem hmem]
        by_cases hBmem : L.X t omega - L.X s omega ∈ B
        · have hAnot : omega ∉ A := fun hAm => hmem ⟨hBmem, hAm⟩
          rw [Set.indicator_of_notMem hAnot, mul_zero]
        · rw [Set.indicator_of_notMem hBmem, zero_mul]
    simp_rw [hfac]
    have hinc_meas : Measurable (fun omega => L.X t omega - L.X s omega) :=
      (hX_meas t).sub (hX_meas s)
    have hf_meas : Measurable[MeasurableSpace.comap (fun omega => L.X t omega - L.X s omega) inferInstance]
        (fun omega => B.indicator (W ((t : ℝ) - (s : ℝ))) (L.X t omega - L.X s omega)) :=
      ((hW_meas _).indicator hB).comp (Measurable.of_comap_le le_rfl)
    have hg_meas : Measurable[F s] (A.indicator (Z s)) :=
      (hZ_measF s).indicator hA
    have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (measurable_iff_comap_le.mp hinc_meas) (F.le s) (L.indepIncrements s t hst) hf_meas hg_meas
    rw [hmul, ← hQ_eq_lintegral s A hA]
  have hQ_inc_preimage : ∀ {s t : NNReal} (hst : s ≤ t) {B : Set ℝ} (hB : MeasurableSet B),
      Q ((fun omega => L.X t omega - L.X s omega) ⁻¹' B) =
        ∫⁻ omega, B.indicator (W ((t : ℝ) - (s : ℝ))) (L.X t omega - L.X s omega) ∂P := by
    intro s t hst B hB
    have h := hQ_inc_inter hst hB MeasurableSet.univ
    simpa [Set.inter_univ, measure_univ] using h
  -- Step 3: Transformed triplet parameters
  let νbeta : Measure ℝ :=
    L.ν.withDensity (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x)))
  let cbeta : ℝ :=
    L.c + beta * L.σ ^ 2 +
      ∫ x in {x : ℝ | |x| < 1}, (Real.exp (beta * x) - 1) * x ∂L.ν
  -- Step 4: νbeta properties
  have hν_Ici : νbeta (Ici 0) = 0 := by
    rw [withDensity_apply _ measurableSet_Ici]
    exact setLIntegral_measure_zero (Ici 0) _ L.ν_Ici
  have hν_ae_neg : ∀ᵐ y ∂L.ν, y < 0 := by
    rw [ae_iff]
    have hset : {y : ℝ | ¬ y < 0} = Ici (0 : ℝ) := by ext y; simp
    rw [hset]
    exact L.ν_Ici
  have hν_integrable : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂νbeta < ⊤ := by
    have hf_meas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x))) := by fun_prop
    have hg_meas : Measurable (fun y : ℝ => ENNReal.ofReal (min 1 (y ^ 2))) := by fun_prop
    rw [lintegral_withDensity_eq_lintegral_mul _ hf_meas hg_meas]
    have hle : ∫⁻ y, ENNReal.ofReal (Real.exp (beta * y)) * ENNReal.ofReal (min 1 (y ^ 2)) ∂L.ν ≤
        ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂L.ν := by
      refine lintegral_mono_ae ?_
      filter_upwards [hν_ae_neg] with y hy
      have hexp1 : ENNReal.ofReal (Real.exp (beta * y)) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hBeta hy.le))
      calc ENNReal.ofReal (Real.exp (beta * y)) * ENNReal.ofReal (min 1 (y ^ 2))
          ≤ 1 * ENNReal.ofReal (min 1 (y ^ 2)) := by gcongr
        _ = ENNReal.ofReal (min 1 (y ^ 2)) := one_mul _
    exact lt_of_le_of_lt hle L.ν_integrable
  -- Step 5: Integrability of min(1, y^2) and the Laplace exponent shift identity
  have hmin_int : Integrable (fun y : ℝ => min 1 (y ^ 2)) L.ν := by
    refine ⟨(by fun_prop : Measurable (fun y : ℝ => min 1 (y ^ 2))).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (fun y : ℝ => ‖min 1 (y ^ 2)‖ₑ) = fun y : ℝ => ENNReal.ofReal (min 1 (y ^ 2)) := by
      ext y
      rw [Real.enorm_eq_ofReal (le_min zero_le_one (sq_nonneg y))]
    simpa only [heq] using L.ν_integrable
  have hjump_int : ∀ a : ℝ, 0 ≤ a →
      IntegrableOn
        (fun y : ℝ => Real.exp (a * y) - 1 - a * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
        (Iio 0) L.ν := by
    intro a ha
    refine Integrable.mono' (hmin_int.integrableOn.const_mul (max 1 (a ^ 2 / 2))) ?_ ?_
    · have hm : Measurable (fun y : ℝ =>
          Real.exp (a * y) - 1 - a * y * (Ioo (-1 : ℝ) 1).indicator 1 y) := by
        have hind : Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
          measurable_const.indicator measurableSet_Ioo
        exact ((Real.measurable_exp.comp (measurable_id.const_mul a)).sub measurable_const).sub
          ((measurable_id.const_mul a).mul hind)
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
      rw [Real.norm_eq_abs]
      exact EsscherSpectralWitnessAux.abs_jumpIntegrand_le ha hy
  have hshift_int :
      IntegrableOn
        (fun y : ℝ => (Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
        (Iio 0) L.ν := by
    refine Integrable.mono' (hmin_int.integrableOn.const_mul beta) ?_ ?_
    · have hind : Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
        measurable_const.indicator measurableSet_Ioo
      have hm : Measurable (fun y : ℝ =>
          (Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) :=
        (((Real.measurable_exp.comp (measurable_id.const_mul beta)).sub measurable_const).mul
          measurable_id).mul hind
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
      rw [Real.norm_eq_abs]
      exact EsscherSpectralWitnessAux.abs_exp_sub_one_mul_le hBeta hy
  have htilted_int : ∀ θ : ℝ, 0 ≤ θ →
      IntegrableOn
        (fun y : ℝ => Real.exp (beta * y) *
          (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y))
        (Iio 0) L.ν := by
    intro θ hθ
    refine Integrable.mono' (hmin_int.integrableOn.const_mul (max 1 (θ ^ 2 / 2))) ?_ ?_
    · have hind : Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
        measurable_const.indicator measurableSet_Ioo
      have hm : Measurable (fun y : ℝ => Real.exp (beta * y) *
          (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)) :=
        (Real.measurable_exp.comp (measurable_id.const_mul beta)).mul
          (((Real.measurable_exp.comp (measurable_id.const_mul θ)).sub measurable_const).sub
            ((measurable_id.const_mul θ).mul hind))
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hexp1 : Real.exp (beta * y) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hBeta hy.le)
      calc Real.exp (beta * y) * |Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y|
          ≤ 1 * (max 1 (θ ^ 2 / 2) * min 1 (y ^ 2)) :=
            mul_le_mul hexp1 (EsscherSpectralWitnessAux.abs_jumpIntegrand_le hθ hy)
              (abs_nonneg _) zero_le_one
        _ = max 1 (θ ^ 2 / 2) * min 1 (y ^ 2) := one_mul _
  have hdrift_set_eq :
      (∫ y in Iio (0 : ℝ), (Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y ∂L.ν) =
      ∫ x in {x : ℝ | |x| < 1}, (Real.exp (beta * x) - 1) * x ∂L.ν := by
    have hind_eq : ∀ y : ℝ,
        (Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y =
          (Ioo (-1 : ℝ) 1).indicator (fun x => (Real.exp (beta * x) - 1) * x) y := by
      intro y
      by_cases hy : y ∈ Ioo (-1 : ℝ) 1
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    simp_rw [hind_eq]
    rw [setIntegral_indicator measurableSet_Ioo]
    have hset_abs : {x : ℝ | |x| < 1} = Ioo (-1 : ℝ) 1 := by
      ext x; simp [abs_lt]
    rw [hset_abs]
    refine setIntegral_congr_set ?_
    filter_upwards [hν_ae_neg] with y hy
    change (y ∈ Iio (0 : ℝ) ∩ Ioo (-1 : ℝ) 1) = (y ∈ Ioo (-1 : ℝ) 1)
    exact propext ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  have hψ_shift : ∀ θ : ℝ, 0 ≤ θ →
      L.ψ (θ + beta) - L.ψ beta = laplaceExponent cbeta L.σ νbeta θ := by
    intro θ hθ
    dsimp only [SpectrallyNegativeLevy.ψ, laplaceExponent]
    have hsub_int :
        (∫ y in Iio (0 : ℝ),
          (Real.exp ((θ + beta) * y) - 1 - (θ + beta) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν) -
        (∫ y in Iio (0 : ℝ),
          (Real.exp (beta * y) - 1 - beta * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν) =
        ∫ y in Iio (0 : ℝ),
          ((Real.exp ((θ + beta) * y) - 1 - (θ + beta) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) -
           (Real.exp (beta * y) - 1 - beta * y * (Ioo (-1 : ℝ) 1).indicator 1 y)) ∂L.ν :=
      (integral_sub (hjump_int (θ + beta) (add_nonneg hθ hBeta)) (hjump_int beta hBeta)).symm
    have hpt : ∀ y : ℝ,
        (Real.exp ((θ + beta) * y) - 1 - (θ + beta) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) -
        (Real.exp (beta * y) - 1 - beta * y * (Ioo (-1 : ℝ) 1).indicator 1 y) =
        Real.exp (beta * y) *
          (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) +
        θ * ((Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) := by
      intro y
      have hexp : Real.exp ((θ + beta) * y) = Real.exp (beta * y) * Real.exp (θ * y) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp]; ring
    have hsplit :
        (∫ y in Iio (0 : ℝ),
          ((Real.exp ((θ + beta) * y) - 1 - (θ + beta) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) -
           (Real.exp (beta * y) - 1 - beta * y * (Ioo (-1 : ℝ) 1).indicator 1 y)) ∂L.ν) =
        (∫ y in Iio (0 : ℝ),
          Real.exp (beta * y) *
            (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν) +
        θ * (∫ y in Iio (0 : ℝ),
          (Real.exp (beta * y) - 1) * y * (Ioo (-1 : ℝ) 1).indicator 1 y ∂L.ν) := by
      simp_rw [hpt]
      rw [integral_add (htilted_int θ hθ) ((hshift_int).const_mul θ), integral_const_mul]
    have hwd :
        (∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂νbeta) =
        ∫ y in Iio (0 : ℝ),
          Real.exp (beta * y) *
            (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν := by
      dsimp only [νbeta]
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
        (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x))))
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _ measurableSet_Iio]
      refine setIntegral_congr_fun measurableSet_Iio fun y _ => ?_
      rw [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    have hcomb :
        (∫ y in Iio (0 : ℝ),
          (Real.exp ((θ + beta) * y) - 1 - (θ + beta) * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν) -
        (∫ y in Iio (0 : ℝ),
          (Real.exp (beta * y) - 1 - beta * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν) =
        (∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂νbeta) +
        θ * (∫ x in {x : ℝ | |x| < 1}, (Real.exp (beta * x) - 1) * x ∂L.ν) := by
      rw [hsub_int, hsplit, hwd, hdrift_set_eq]
    dsimp only [cbeta]
    linarith
  -- Step 6: Marginal law of X_t under Q and Laplace transform under Q
  have hQ_map_eq : ∀ t : NNReal,
      Q.map (L.X t) =
        (P.map (L.X t)).withDensity
          (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x - L.ψ beta * (t : ℝ)))) := by
    intro t
    ext B hB
    rw [Measure.map_apply (hX_meas t) hB,
      withDensity_apply _ hB,
      setLIntegral_map hB (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x - L.ψ beta * (t : ℝ))))) (hX_meas t),
      ← lintegral_indicator (hX_meas t hB)]
    exact hQ_eq_lintegral t (L.X t ⁻¹' B) (hX_measF (le_refl t) hB)
  have hlaplace_Q : ∀ (t : NNReal) (θ : ℝ), 0 ≤ θ →
      Integrable (fun omega => Real.exp (θ * L.X t omega)) Q ∧
        ∫ omega, Real.exp (θ * L.X t omega) ∂Q =
          Real.exp ((t : ℝ) * laplaceExponent cbeta L.σ νbeta θ) := by
    intro t θ hθ
    have hexp_meas : Measurable (fun omega => Real.exp (θ * L.X t omega)) :=
      Real.measurable_exp.comp ((hX_meas t).const_mul θ)
    have hlint :
        (∫⁻ omega, ENNReal.ofReal (Real.exp (θ * L.X t omega)) ∂Q) =
        ENNReal.ofReal (Real.exp ((t : ℝ) * laplaceExponent cbeta L.σ νbeta θ)) := by
      have hg_meas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x))) := by fun_prop
      have hd_meas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x - L.ψ beta * (t : ℝ)))) := by
        fun_prop
      rw [← lintegral_map hg_meas (hX_meas t), hQ_map_eq t,
        lintegral_withDensity_eq_lintegral_mul _ hd_meas hg_meas]
      dsimp only [Pi.mul_apply]
      rw [lintegral_map (by fun_prop : Measurable (fun x : ℝ =>
        ENNReal.ofReal (Real.exp (beta * x - L.ψ beta * (t : ℝ))) *
          ENNReal.ofReal (Real.exp (θ * x)))) (hX_meas t)]
      have hfac : ∀ omega,
          ENNReal.ofReal (Real.exp (beta * L.X t omega - L.ψ beta * (t : ℝ))) *
            ENNReal.ofReal (Real.exp (θ * L.X t omega)) =
          ENNReal.ofReal (Real.exp (-(L.ψ beta * (t : ℝ)))) *
            ENNReal.ofReal (Real.exp ((θ + beta) * L.X t omega)) := by
        intro omega
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_mul (Real.exp_nonneg _),
          ← Real.exp_add, ← Real.exp_add]
        congr 2; ring
      simp_rw [hfac]
      rw [lintegral_const_mul _ (by
        have := hX_meas t
        fun_prop)]
      rcases L.laplace t (θ + beta) (add_nonneg hθ hBeta) with ⟨hintP, hvalP⟩
      rw [← ofReal_integral_eq_lintegral_ofReal hintP (ae_of_all _ fun _ => Real.exp_nonneg _),
        hvalP, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      have hsh := hψ_shift θ hθ
      dsimp only [SpectrallyNegativeLevy.ψ] at hsh ⊢
      rw [← hsh]
      ring
    have hintQ : Integrable (fun omega => Real.exp (θ * L.X t omega)) Q := by
      refine ⟨hexp_meas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      have heq : (fun omega => ‖Real.exp (θ * L.X t omega)‖ₑ) =
          fun omega => ENNReal.ofReal (Real.exp (θ * L.X t omega)) := by
        ext omega
        rw [Real.enorm_eq_ofReal (Real.exp_nonneg _)]
      rw [heq, hlint]
      exact ENNReal.ofReal_lt_top
    refine ⟨hintQ, ?_⟩
    have hpos : 0 ≤ ∫ omega, Real.exp (θ * L.X t omega) ∂Q :=
      integral_nonneg fun _ => Real.exp_nonneg _
    have hofReal : ENNReal.ofReal (∫ omega, Real.exp (θ * L.X t omega) ∂Q) =
        ENNReal.ofReal (Real.exp ((t : ℝ) * laplaceExponent cbeta L.σ νbeta θ)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hintQ (ae_of_all _ fun _ => Real.exp_nonneg _), hlint]
    exact (ENNReal.ofReal_eq_ofReal_iff hpos (Real.exp_nonneg _)).mp hofReal
  -- Step 7: Assemble Lbeta : SpectrallyNegativeLevy Q F
  refine ⟨{
    X := L.X
    c := cbeta
    σ := L.σ
    ν := νbeta
    isProbability := inferInstance
    σ_nonneg := L.σ_nonneg
    ν_Ici := hν_Ici
    ν_integrable := hν_integrable
    X_zero := L.X_zero
    rightCont := L.rightCont
    leftLim := L.leftLim
    noPosJumps := L.noPosJumps
    adapted := L.adapted
    indepIncrements := fun s t hst => by
      rw [Indep_iff]
      intro s1 s2 hs1 hs2
      rcases hs1 with ⟨B, hB, rfl⟩
      rw [hQ_inc_inter hst hB hs2, hQ_inc_preimage hst hB]
    stationaryIncrements := fun s t hst => by
      have hinc_meas : Measurable (fun omega => L.X t omega - L.X s omega) :=
        (hX_meas t).sub (hX_meas s)
      refine ⟨hinc_meas.aemeasurable, (hX_meas (t - s)).aemeasurable, ?_⟩
      ext B hB
      rw [Measure.map_apply hinc_meas hB, Measure.map_apply (hX_meas (t - s)) hB,
        hQ_inc_preimage hst hB, hQ_eq_lintegral (t - s) (L.X (t - s) ⁻¹' B)
          (hX_measF (le_refl (t - s)) hB)]
      have hd : (t : ℝ) - (s : ℝ) = ((t - s : NNReal) : ℝ) := (NNReal.coe_sub hst).symm
      rw [hd]
      have hg_meas : Measurable (B.indicator (W ((t - s : NNReal) : ℝ))) :=
        (hW_meas _).indicator hB
      rw [← lintegral_map hg_meas hinc_meas, (L.stationaryIncrements s t hst).map_eq,
        lintegral_map hg_meas (hX_meas (t - s))]
      refine lintegral_congr fun omega => ?_
      by_cases hmem : L.X (t - s) omega ∈ B
      · have hmem' : omega ∈ L.X (t - s) ⁻¹' B := hmem
        simp [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem', W, Z, esscherDensity]
      · have hmem' : omega ∉ L.X (t - s) ⁻¹' B := hmem
        simp [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']
    laplace := hlaplace_Q
  }, rfl, rfl, rfl, rfl⟩
