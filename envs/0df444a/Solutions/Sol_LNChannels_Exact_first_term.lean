-- Prove2me | solution 1 for LNChannels.Exact.first_term
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:10:53.860014+00:00
-- url     : https://prove2.me/submissions/130fcd67-3c87-4614-8578-1d3be0dfa000

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LNHelp

lemma integral_expMeasure (lam : ℝ) (hlam : 0 < lam) (g : ℝ → ℝ) :
    ∫ x, g x ∂(expMeasure lam) = ∫ x, exponentialPDFReal lam x * g x := by
  unfold expMeasure gammaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (f := gammaPDF 1 lam)
    ((measurable_gammaPDFReal 1 lam).ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hlam x)]
  rfl

lemma noAtoms_exp (b : ℝ) : NullSingletonClass (expMeasure b) := by
  unfold expMeasure gammaMeasure
  exact ⟨fun x => (withDensity_absolutelyContinuous _ _) (Real.volume_singleton)⟩

lemma ae_nonneg_exp (b : ℝ) : ∀ᵐ x ∂(expMeasure b), 0 ≤ x := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext a; simp
  rw [this]
  unfold expMeasure gammaMeasure
  rw [withDensity_apply _ measurableSet_Iio]
  exact lintegral_exponentialPDF_of_nonpos (le_refl 0)

lemma real_Ici_exp (b : ℝ) (hb : 0 < b) (x : ℝ) (hx : 0 ≤ x) :
    (expMeasure b).real (Set.Ici x) = Real.exp (-(b * x)) := by
  have := isProbabilityMeasure_expMeasure hb
  have := noAtoms_exp b
  have h2 : (expMeasure b).real (Set.Iic x) = 1 - Real.exp (-(b * x)) := by
    rw [← cdf_eq_real, cdf_expMeasure_eq hb, if_pos hx]
  rw [← Set.compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio,
    measureReal_congr Iio_ae_eq_Iic, h2]
  ring

lemma inner_le (r b : ℝ) (hb : 0 < b) (x : ℝ) (hx : 0 ≤ x) :
    ∫ y, (if x ≤ y then Real.exp (-r * min x y) else 0) ∂(expMeasure b)
      = Real.exp (-(r + b) * x) := by
  have := isProbabilityMeasure_expMeasure hb
  have : (fun y => if x ≤ y then Real.exp (-r * min x y) else 0)
      = (Set.Ici x).indicator (fun _ => Real.exp (-r * x)) := by
    ext y
    by_cases h : x ≤ y
    · simp [Set.indicator, h, min_eq_left h]
    · simp [Set.indicator, h]
  rw [this, integral_indicator_const _ measurableSet_Ici, real_Ici_exp b hb x hx, smul_eq_mul,
    ← Real.exp_add]
  congr 1; ring

lemma inner_lt (r b : ℝ) (hb : 0 < b) (x : ℝ) (hx : 0 ≤ x) :
    ∫ y, (if x < y then Real.exp (-r * min x y) else 0) ∂(expMeasure b)
      = Real.exp (-(r + b) * x) := by
  rw [← inner_le r b hb x hx]
  have := noAtoms_exp b
  apply integral_congr_ae
  have hne : ∀ᵐ y ∂(expMeasure b), y ≠ x := by
    rw [ae_iff]
    simpa using measure_singleton (μ := expMeasure b) x
  filter_upwards [hne] with y hy
  by_cases h : x ≤ y
  · have h' : x < y := lt_of_le_of_ne h (Ne.symm hy)
    simp [h, h']
  · have h' : ¬ x < y := fun h'' => h h''.le
    simp [h, h']

lemma outer (r la lb : ℝ) (hr : 0 < r) (hla : 0 < la) (hlb : 0 < lb) (G : ℝ → ℝ)
    (hG : ∀ x, 0 ≤ x → G x = Real.exp (-(r + lb) * x)) :
    ∫ x, G x ∂(expMeasure la) = la / (r + la + lb) := by
  rw [integral_expMeasure la hla]
  have hS : 0 < r + la + lb := by linarith
  have : (fun x => exponentialPDFReal la x * G x)
      = (Set.Ici (0:ℝ)).indicator (fun x => la * Real.exp (-(r + la + lb) * x)) := by
    ext x
    by_cases hx : 0 ≤ x
    · have hp : exponentialPDFReal la x = la * Real.exp (-(la * x)) := by
        simp [exponentialPDFReal, gammaPDFReal, hx]
      rw [hp, hG x hx, Set.indicator_of_mem (show x ∈ Set.Ici (0:ℝ) from hx), mul_assoc,
        ← Real.exp_add]
      congr 2; ring
    · have hp : exponentialPDFReal la x = 0 := by
        simp [exponentialPDFReal, gammaPDFReal, hx]
      rw [hp, Set.indicator_of_notMem (show x ∉ Set.Ici (0:ℝ) from hx)]
      simp
  rw [this, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_exp_mul_Ioi (a := -(r + la + lb)) (by linarith) 0]
  rw [mul_zero, Real.exp_zero, neg_div_neg_eq]
  ring

lemma ae_nonneg_law {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (τ : Ω → ℝ) (l : ℝ)
    (hτ : Measurable τ) (hlaw : P.map τ = expMeasure l) : ∀ᵐ ω ∂P, 0 ≤ τ ω := by
  have h1 : ∀ᵐ x ∂(P.map τ), 0 ≤ x := by rw [hlaw]; exact ae_nonneg_exp l
  exact ae_of_ae_map hτ.aemeasurable h1

lemma exp_le_one' (r x y : ℝ) (hr : 0 < r) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.exp (-r * min x y) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have := le_min hx hy
  nlinarith

lemma transfer {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τa τb : Ω → ℝ) (la lb : ℝ) (hla : 0 < la) (hlb : 0 < lb)
    (hτa : Measurable τa) (hτb : Measurable τb)
    (hlawa : P.map τa = expMeasure la) (hlawb : P.map τb = expMeasure lb)
    (hindep : IndepFun τa τb P) (F : ℝ → ℝ → ℝ) (hF : Measurable (fun p : ℝ × ℝ => F p.1 p.2))
    (hbd : ∀ x y, 0 ≤ x → 0 ≤ y → |F x y| ≤ 1) :
    Integrable (fun ω => F (τa ω) (τb ω)) P ∧
    ∫ ω, F (τa ω) (τb ω) ∂P = ∫ x, ∫ y, F x y ∂(expMeasure lb) ∂(expMeasure la) := by
  have := isProbabilityMeasure_expMeasure hla
  have := isProbabilityMeasure_expMeasure hlb
  have hjoint : P.map (fun ω => (τa ω, τb ω)) = (expMeasure la).prod (expMeasure lb) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hτa.aemeasurable hτb.aemeasurable).1 hindep,
      hlawa, hlawb]
  have hmeas : Measurable (fun ω => (τa ω, τb ω)) := hτa.prodMk hτb
  have hae : ∀ᵐ ω ∂P, 0 ≤ τa ω ∧ 0 ≤ τb ω := by
    filter_upwards [ae_nonneg_law P τa la hτa hlawa, ae_nonneg_law P τb lb hτb hlawb]
      with ω a b using ⟨a, b⟩
  have hint : Integrable (fun ω => F (τa ω) (τb ω)) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) (hF.comp hmeas).aestronglyMeasurable ?_
    filter_upwards [hae] with ω h
    rw [Real.norm_eq_abs]
    exact hbd _ _ h.1 h.2
  have hintP : Integrable (fun p : ℝ × ℝ => F p.1 p.2)
      ((expMeasure la).prod (expMeasure lb)) := by
    rw [← hjoint]
    exact (integrable_map_measure hF.aestronglyMeasurable hmeas.aemeasurable).2 hint
  refine ⟨hint, ?_⟩
  calc ∫ ω, F (τa ω) (τb ω) ∂P
      = ∫ p, F p.1 p.2 ∂(P.map (fun ω => (τa ω, τb ω))) :=
        (integral_map hmeas.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ x, ∫ y, F x y ∂(expMeasure lb) ∂(expMeasure la) := by
        rw [hjoint, integral_prod _ hintP]

theorem last_aux {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ₁ τ₂ : Ω → ℝ) (lam₁ lam₂ r : ℝ) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hr : 0 < r)
    (hτ₁ : Measurable τ₁) (hτ₂ : Measurable τ₂)
    (hlaw₁ : P.map τ₁ = expMeasure lam₁) (hlaw₂ : P.map τ₂ = expMeasure lam₂)
    (hindep : IndepFun τ₂ τ₁ P) (J : ℤ → ℝ) (n : ℤ) :
    ∫ ω, Real.exp (-r * min (τ₂ ω) (τ₁ ω)) * J (if τ₂ ω < τ₁ ω then n + 1 else n - 1) ∂P
      = J (n + 1) * (lam₂ / (r + lam₂ + lam₁))
        + J (n - 1) * (lam₁ / (r + lam₂ + lam₁)) := by
  have hm1 : Measurable (fun p : ℝ × ℝ =>
      (fun x y : ℝ => if x < y then Real.exp (-r * min x y) else 0) p.1 p.2) := by
    refine Measurable.ite (measurableSet_lt measurable_fst measurable_snd) ?_ measurable_const
    fun_prop
  have hm2 : Measurable (fun p : ℝ × ℝ =>
      (fun x y : ℝ => if x ≤ y then Real.exp (-r * min x y) else 0) p.1 p.2) := by
    refine Measurable.ite (measurableSet_le measurable_fst measurable_snd) ?_ measurable_const
    fun_prop
  have hb1 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      |(fun x y : ℝ => if x < y then Real.exp (-r * min x y) else 0) x y| ≤ 1 := by
    intro x y hx hy
    dsimp only
    split_ifs
    · rw [abs_of_pos (Real.exp_pos _)]; exact exp_le_one' r x y hr hx hy
    · simp
  have hb2 : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      |(fun x y : ℝ => if x ≤ y then Real.exp (-r * min x y) else 0) x y| ≤ 1 := by
    intro x y hx hy
    dsimp only
    split_ifs
    · rw [abs_of_pos (Real.exp_pos _)]; exact exp_le_one' r x y hr hx hy
    · simp
  obtain ⟨hi1, he1⟩ := transfer P τ₂ τ₁ lam₂ lam₁ hlam₂ hlam₁ hτ₂ hτ₁ hlaw₂ hlaw₁ hindep
    (fun x y : ℝ => if x < y then Real.exp (-r * min x y) else 0) hm1 hb1
  obtain ⟨hi2, he2⟩ := transfer P τ₁ τ₂ lam₁ lam₂ hlam₁ hlam₂ hτ₁ hτ₂ hlaw₁ hlaw₂ hindep.symm
    (fun x y : ℝ => if x ≤ y then Real.exp (-r * min x y) else 0) hm2 hb2
  rw [outer r lam₂ lam₁ hr hlam₂ hlam₁ _ (fun x hx => inner_lt r lam₁ hlam₁ x hx)] at he1
  rw [outer r lam₁ lam₂ hr hlam₁ hlam₂ _ (fun x hx => inner_le r lam₂ hlam₂ x hx)] at he2
  have hpt : ∀ ω, Real.exp (-r * min (τ₂ ω) (τ₁ ω)) * J (if τ₂ ω < τ₁ ω then n + 1 else n - 1)
      = J (n + 1) * (fun x y : ℝ => if x < y then Real.exp (-r * min x y) else 0) (τ₂ ω) (τ₁ ω)
        + J (n - 1) * (fun x y : ℝ => if x ≤ y then Real.exp (-r * min x y) else 0)
            (τ₁ ω) (τ₂ ω) := by
    intro ω
    dsimp only
    by_cases h : τ₂ ω < τ₁ ω
    · have h' : ¬ τ₁ ω ≤ τ₂ ω := not_le.2 h
      simp [h, h']
      ring
    · have h' : τ₁ ω ≤ τ₂ ω := not_lt.1 h
      simp only [h, h', if_false, if_true]
      rw [min_comm]
      ring
  have hfun : (fun ω => Real.exp (-r * min (τ₂ ω) (τ₁ ω)) *
      J (if τ₂ ω < τ₁ ω then n + 1 else n - 1)) = fun ω =>
      J (n + 1) * (fun x y : ℝ => if x < y then Real.exp (-r * min x y) else 0) (τ₂ ω) (τ₁ ω)
        + J (n - 1) * (fun x y : ℝ => if x ≤ y then Real.exp (-r * min x y) else 0)
            (τ₁ ω) (τ₂ ω) := funext hpt
  rw [hfun, integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
    integral_const_mul, he1, he2]
  have : r + lam₁ + lam₂ = r + lam₂ + lam₁ := by ring
  rw [this]

theorem first_aux {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ₁ τ₂ : Ω → ℝ) (lam₁ lam₂ r : ℝ) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hr : 0 < r)
    (hτ₁ : Measurable τ₁) (hτ₂ : Measurable τ₂)
    (hlaw₁ : P.map τ₁ = expMeasure lam₁) (hlaw₂ : P.map τ₂ = expMeasure lam₂)
    (hindep : IndepFun τ₂ τ₁ P) (l₁ l₂ : ℕ) :
    ∫ ω, Real.exp (-r * min (τ₂ ω) (τ₁ ω)) ∂P = (lam₂ + lam₁) / (lam₂ + lam₁ + r) ∧
    ∫ ω, (∫ s in (0 : ℝ)..(min (τ₂ ω) (τ₁ ω)), Real.exp (-r * s) * r * ((l₁ : ℝ) + l₂)) ∂P
      = ((l₁ : ℝ) + l₂) * (r / (r + lam₂ + lam₁)) := by
  have h1 : ∫ ω, Real.exp (-r * min (τ₂ ω) (τ₁ ω)) ∂P = (lam₂ + lam₁) / (lam₂ + lam₁ + r) := by
    have h := last_aux P τ₁ τ₂ lam₁ lam₂ r hlam₁ hlam₂ hr hτ₁ hτ₂ hlaw₁ hlaw₂ hindep
      (fun _ => (1 : ℝ)) 0
    simp only [mul_one, one_mul] at h
    rw [h]
    have : r + lam₂ + lam₁ = lam₂ + lam₁ + r := by ring
    rw [this]
    ring
  refine ⟨h1, ?_⟩
  have hE : Integrable (fun ω => Real.exp (-r * min (τ₂ ω) (τ₁ ω))) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · exact (Real.measurable_exp.comp (measurable_const.mul (hτ₂.min hτ₁))).aestronglyMeasurable
    · filter_upwards [ae_nonneg_law P τ₂ lam₂ hτ₂ hlaw₂, ae_nonneg_law P τ₁ lam₁ hτ₁ hlaw₁]
        with ω a b
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_le_one' r _ _ hr a b
  have hI : ∀ m : ℝ, ∫ s in (0 : ℝ)..m, Real.exp (-r * s) * r * ((l₁ : ℝ) + l₂)
      = ((l₁ : ℝ) + l₂) * (1 - Real.exp (-r * m)) := by
    intro m
    have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => -(((l₁ : ℝ) + l₂)) * Real.exp (-r * s))
        (Real.exp (-r * s) * r * ((l₁ : ℝ) + l₂)) s := by
      intro s
      have := (((hasDerivAt_id s).const_mul (-r)).exp).const_mul (-(((l₁ : ℝ) + l₂)))
      refine this.congr_deriv ?_
      simp only [id]
      ring
    have hc : Continuous (fun s : ℝ => Real.exp (-r * s) * r * ((l₁ : ℝ) + l₂)) := by fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (hc.intervalIntegrable _ _)]
    simp only [mul_zero, Real.exp_zero]
    ring
  have hfun : (fun ω => ∫ s in (0 : ℝ)..(min (τ₂ ω) (τ₁ ω)),
      Real.exp (-r * s) * r * ((l₁ : ℝ) + l₂))
      = fun ω => ((l₁ : ℝ) + l₂) * (1 - Real.exp (-r * min (τ₂ ω) (τ₁ ω))) :=
    funext fun ω => hI _
  rw [hfun, integral_const_mul, integral_sub (integrable_const _) hE, h1]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hpos : 0 < lam₂ + lam₁ + r := by linarith
  have : r + lam₂ + lam₁ = lam₂ + lam₁ + r := by ring
  rw [this]
  field_simp
  ring

end LNHelp

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ₁ τ₂ : Ω → ℝ) (lam₁ lam₂ r : ℝ) (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hr : 0 < r)
    (hτ₁ : Measurable τ₁) (hτ₂ : Measurable τ₂)
    (hlaw₁ : P.map τ₁ = expMeasure lam₁) (hlaw₂ : P.map τ₂ = expMeasure lam₂)
    (hindep : IndepFun τ₂ τ₁ P) (l₁ l₂ : ℕ) :
    ∫ ω, Real.exp (-r * min (τ₂ ω) (τ₁ ω)) ∂P = (lam₂ + lam₁) / (lam₂ + lam₁ + r) ∧
    ∫ ω, (∫ s in (0 : ℝ)..(min (τ₂ ω) (τ₁ ω)), Real.exp (-r * s) * r * ((l₁ : ℝ) + l₂)) ∂P
      = ((l₁ : ℝ) + l₂) * (r / (r + lam₂ + lam₁)) :=
  LNHelp.first_aux P τ₁ τ₂ lam₁ lam₂ r hlam₁ hlam₂ hr hτ₁ hτ₂ hlaw₁ hlaw₂ hindep l₁ l₂
