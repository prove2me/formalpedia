-- Prove2me | solution 1 for MartOT.Shadow.lemma_4_16
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:09:34.02717+00:00
-- url     : https://prove2.me/submissions/5e24c494-b716-4035-8aac-dca8bb8c3e59

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace Lemma416Helpers

open MeasureTheory NNReal Filter Topology Set

private abbrev mass (μ : Measure ℝ) : ℝ := (μ Set.univ).toReal

private noncomputable def mean (μ : Measure ℝ) : ℝ := ∫ y, y ∂μ

private noncomputable def rderiv (f : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin f (Ioi x) x

private noncomputable def convEnv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ k : ℝ → ℝ, ConvexOn ℝ Set.univ k ∧ (∀ z, k z ≤ f z) ∧ k x = y}

/-! ### Section A: Basic properties of `InM`, `integralE`, `ConvexLE`, `ExtConvexLE` -/

private lemma inM_integrable_abs {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    Integrable (fun y : ℝ => |y|) μ := by
  simpa [Real.norm_eq_abs] using hμ.2.norm

private lemma inM_integrable_sub_abs {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    Integrable (fun y : ℝ => |y - x|) μ := by
  have := hμ.1
  simpa [Real.norm_eq_abs] using (hμ.2.sub (integrable_const x)).norm

private lemma inM_integrable_max_sub {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    Integrable (fun y : ℝ => max (y - x) 0) μ := by
  have := hμ.1
  exact (hμ.2.sub (integrable_const x)).sup (integrable_const 0)

private lemma inM_integrable_max_sub' {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    Integrable (fun y : ℝ => max (x - y) 0) μ := by
  have := hμ.1
  exact ((integrable_const x).sub hμ.2).sup (integrable_const 0)

private lemma inM_of_le {μ ν : Measure ℝ} (hle : μ ≤ ν) (hν : MartOT.Var.InM ν) :
    MartOT.Var.InM μ := by
  have := hν.1
  exact ⟨isFiniteMeasure_of_le ν hle, hν.2.mono_measure hle⟩

private lemma inM_add {μ ν : Measure ℝ} (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) :
    MartOT.Var.InM (μ + ν) := by
  have := hμ.1
  have := hν.1
  exact ⟨inferInstance, hμ.2.add_measure hν.2⟩

private lemma inM_smul_dirac (α : ℝ≥0) (x : ℝ) :
    MartOT.Var.InM ((α : ENNReal) • Measure.dirac x) := by
  refine ⟨⟨?_⟩, ?_⟩
  · simp [ENNReal.coe_lt_top]
  · exact (integrable_dirac (a := x) (by simp)).smul_measure ENNReal.coe_ne_top

private lemma integralE_eq_coe {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f μ) :
    MartOT.Var.integralE μ f = ((∫ y, f y ∂μ : ℝ) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have hpos_eq : (∫⁻ y, ((f y : EReal)).toENNReal ∂μ) = ∫⁻ y, ENNReal.ofReal (f y) ∂μ := rfl
  have hneg_eq : (∫⁻ y, (-(f y : EReal)).toENNReal ∂μ) = ∫⁻ y, ENNReal.ofReal (-f y) ∂μ :=
    lintegral_congr fun y => by rw [← EReal.coe_neg, EReal.real_coe_toENNReal]
  rw [hpos_eq, hneg_eq]
  have hp_lt : ∫⁻ y, ENNReal.ofReal (f y) ∂μ < ⊤ := by
    calc ∫⁻ y, ENNReal.ofReal (f y) ∂μ
        ≤ ∫⁻ y, ‖f y‖ₑ ∂μ := lintegral_mono fun y => by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ < ⊤ := hf.2
  have hn_lt : ∫⁻ y, ENNReal.ofReal (-f y) ∂μ < ⊤ := by
    calc ∫⁻ y, ENNReal.ofReal (-f y) ∂μ
        ≤ ∫⁻ y, ‖f y‖ₑ ∂μ := lintegral_mono fun y => by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
      _ < ⊤ := hf.2
  rw [← ENNReal.ofReal_toReal hp_lt.ne, ← ENNReal.ofReal_toReal hn_lt.ne]
  rw [EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal]
  rw [max_eq_left ENNReal.toReal_nonneg, max_eq_left ENNReal.toReal_nonneg]
  rw [← EReal.coe_sub, ← integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]

private lemma integralE_add_integrable {μ : Measure ℝ} {f a : ℝ → ℝ}
    (hf_meas : Measurable f) (hf0 : ∀ y, 0 ≤ f y) (ha : Integrable a μ) :
    MartOT.Var.integralE μ (fun y => f y + a y) =
      ((∫⁻ y, ENNReal.ofReal (f y) ∂μ : ENNReal) : EReal) + ((∫ y, a y ∂μ : ℝ) : EReal) := by
  by_cases htop : ∫⁻ y, ENNReal.ofReal (f y) ∂μ = ⊤
  · rw [htop, EReal.coe_ennreal_top]
    have hbot : ((∫ y, a y ∂μ : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
    rw [EReal.top_add_of_ne_bot hbot]
    unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
    have hpos_eq : (∫⁻ y, (((f y + a y : ℝ) : EReal)).toENNReal ∂μ) =
        ∫⁻ y, ENNReal.ofReal (f y + a y) ∂μ := rfl
    have hneg_eq : (∫⁻ y, (-((f y + a y : ℝ) : EReal)).toENNReal ∂μ) =
        ∫⁻ y, ENNReal.ofReal (-(f y + a y)) ∂μ :=
      lintegral_congr fun y => by rw [← EReal.coe_neg, EReal.real_coe_toENNReal]
    rw [hpos_eq, hneg_eq]
    have han_lt : ∫⁻ y, ENNReal.ofReal (-a y) ∂μ < ⊤ := by
      calc ∫⁻ y, ENNReal.ofReal (-a y) ∂μ
          ≤ ∫⁻ y, ‖a y‖ₑ ∂μ := lintegral_mono fun y => by
            rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
        _ < ⊤ := ha.2
    have hneg_lt : ∫⁻ y, ENNReal.ofReal (-(f y + a y)) ∂μ < ⊤ := by
      calc ∫⁻ y, ENNReal.ofReal (-(f y + a y)) ∂μ
          ≤ ∫⁻ y, ENNReal.ofReal (-a y) ∂μ := lintegral_mono fun y =>
            ENNReal.ofReal_le_ofReal (by linarith [hf0 y])
        _ < ⊤ := han_lt
    have hpos_top : ∫⁻ y, ENNReal.ofReal (f y + a y) ∂μ = ⊤ := by
      by_contra hne
      have hmax : ∀ r : ℝ, ENNReal.ofReal (max r 0) = ENNReal.ofReal r := fun r => by
        rcases le_total r 0 with hr | hr
        · rw [max_eq_right hr, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos hr]
        · rw [max_eq_left hr]
      have hle : ∫⁻ y, ENNReal.ofReal (f y) ∂μ ≤
          (∫⁻ y, ENNReal.ofReal (f y + a y) ∂μ) + ∫⁻ y, ENNReal.ofReal (-a y) ∂μ := by
        calc ∫⁻ y, ENNReal.ofReal (f y) ∂μ
            ≤ ∫⁻ y, (ENNReal.ofReal (f y + a y) + ENNReal.ofReal (-a y)) ∂μ :=
              lintegral_mono fun y => by
                have h1 : f y ≤ max (f y + a y) 0 + max (-a y) 0 := by
                  linarith [le_max_left (f y + a y) 0, le_max_left (-a y) 0]
                calc ENNReal.ofReal (f y)
                    ≤ ENNReal.ofReal (max (f y + a y) 0 + max (-a y) 0) :=
                      ENNReal.ofReal_le_ofReal h1
                  _ = ENNReal.ofReal (max (f y + a y) 0) + ENNReal.ofReal (max (-a y) 0) :=
                      ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)
                  _ = ENNReal.ofReal (f y + a y) + ENNReal.ofReal (-a y) := by
                      rw [hmax, hmax]
          _ = (∫⁻ y, ENNReal.ofReal (f y + a y) ∂μ) + ∫⁻ y, ENNReal.ofReal (-a y) ∂μ :=
              lintegral_add_left' (ENNReal.measurable_ofReal.comp_aemeasurable
                (hf_meas.aemeasurable.add ha.1.aemeasurable)) _
      rw [htop] at hle
      exact not_lt_of_ge hle (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hne, han_lt⟩)
    rw [hpos_top, EReal.coe_ennreal_top, sub_eq_add_neg]
    have hne_top : ((∫⁻ y, ENNReal.ofReal (-(f y + a y)) ∂μ : ENNReal) : EReal) ≠ ⊤ := by
      simpa using hneg_lt.ne
    exact EReal.top_add_of_ne_bot fun heq => hne_top (by simpa using congrArg Neg.neg heq)
  · have hf_int : Integrable f μ := by
      refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
      show ∫⁻ y, ‖f y‖ₑ ∂μ < ⊤
      have h_eq : (∫⁻ y, ‖f y‖ₑ ∂μ) = ∫⁻ y, ENNReal.ofReal (f y) ∂μ := by
        congr 1; ext y; rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf0 y)]
      rw [h_eq]
      exact lt_top_iff_ne_top.mpr htop
    have hfa : Integrable (fun y => f y + a y) μ := hf_int.add ha
    rw [integralE_eq_coe hfa, integral_add hf_int ha, EReal.coe_add]
    congr 1
    rw [← ofReal_integral_eq_lintegral_ofReal hf_int (Eventually.of_forall hf0)]
    rw [EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg hf0)]

private lemma convexOn_neg_id : ConvexOn ℝ Set.univ (fun y : ℝ => -y) := by
  refine ⟨convex_univ, fun x _ y _ a b _ _ _ => ?_⟩
  simp only [smul_eq_mul]; linarith

private lemma convexOn_abs_sub (x : ℝ) : ConvexOn ℝ Set.univ (fun y : ℝ => |y - x|) := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h1 : a * y₁ + b * y₂ - x = a * (y₁ - x) + b * (y₂ - x) := by
    calc a * y₁ + b * y₂ - x = a * y₁ + b * y₂ - (a + b) * x := by rw [hab, one_mul]
      _ = a * (y₁ - x) + b * (y₂ - x) := by ring
  rw [h1]
  calc |a * (y₁ - x) + b * (y₂ - x)|
      ≤ |a * (y₁ - x)| + |b * (y₂ - x)| := abs_add_le _ _
    _ = a * |y₁ - x| + b * |y₂ - x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

private lemma convexOn_max_sub (x : ℝ) : ConvexOn ℝ Set.univ (fun y : ℝ => max (y - x) 0) := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h1 : a * y₁ + b * y₂ - x = a * (y₁ - x) + b * (y₂ - x) := by
    calc a * y₁ + b * y₂ - x = a * y₁ + b * y₂ - (a + b) * x := by rw [hab, one_mul]
      _ = a * (y₁ - x) + b * (y₂ - x) := by ring
  rw [h1]
  refine max_le ?_ (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)

private lemma convexOn_max_sub' (x : ℝ) : ConvexOn ℝ Set.univ (fun y : ℝ => max (x - y) 0) := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h1 : x - (a * y₁ + b * y₂) = a * (x - y₁) + b * (x - y₂) := by
    calc x - (a * y₁ + b * y₂) = (a + b) * x - (a * y₁ + b * y₂) := by rw [hab, one_mul]
      _ = a * (x - y₁) + b * (x - y₂) := by ring
  rw [h1]
  refine max_le ?_ (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)

private lemma convexLE_mass_eq {μ ν : Measure ℝ} (h : MartOT.Var.ConvexLE μ ν) :
    mass μ = mass ν := by
  have := h.1.1
  have := h.2.1.1
  have h1 := h.2.2 (fun _ => (1 : ℝ)) (convexOn_const 1 convex_univ)
  have h2 := h.2.2 (fun _ => (-1 : ℝ)) (convexOn_const (-1) convex_univ)
  rw [integralE_eq_coe (integrable_const 1), integralE_eq_coe (integrable_const 1)] at h1
  rw [integralE_eq_coe (integrable_const (-1)), integralE_eq_coe (integrable_const (-1))] at h2
  simp only [EReal.coe_le_coe_iff, integral_const, smul_eq_mul, mul_one, mul_neg,
    Measure.real_def] at h1 h2
  linarith

private lemma convexLE_mean_eq {μ ν : Measure ℝ} (h : MartOT.Var.ConvexLE μ ν) :
    mean μ = mean ν := by
  have h1 := h.2.2 (fun y => y) (convexOn_id convex_univ)
  have h2 := h.2.2 (fun y => -y) convexOn_neg_id
  have hnμ : Integrable (fun y : ℝ => -y) μ := h.1.2.neg
  have hnν : Integrable (fun y : ℝ => -y) ν := h.2.1.2.neg
  rw [integralE_eq_coe h.1.2, integralE_eq_coe h.2.1.2, EReal.coe_le_coe_iff] at h1
  rw [integralE_eq_coe hnμ, integralE_eq_coe hnν, EReal.coe_le_coe_iff,
    integral_neg, integral_neg] at h2
  unfold mean
  linarith

private lemma convexLE_potential_le {μ ν : Measure ℝ} (h : MartOT.Var.ConvexLE μ ν) (x : ℝ) :
    MartOT.Var.potential μ x ≤ MartOT.Var.potential ν x := by
  have h1 := h.2.2 (fun y => |y - x|) (convexOn_abs_sub x)
  rw [integralE_eq_coe (inM_integrable_sub_abs h.1 x),
    integralE_eq_coe (inM_integrable_sub_abs h.2.1 x), EReal.coe_le_coe_iff] at h1
  exact h1

private lemma convexLE_imp_extConvexLE {μ ν : Measure ℝ} (h : MartOT.Var.ConvexLE μ ν) :
    MartOT.Var.ExtConvexLE μ ν := by
  refine ⟨h.1, h.2.1, fun ϕ hϕ hϕ0 => ?_⟩
  have hle := h.2.2 ϕ hϕ
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral at hle
  have hzero : ∀ (m : Measure ℝ), (∫⁻ y, (-(ϕ y : EReal)).toENNReal ∂m) = 0 := fun m =>
    (lintegral_congr fun y => by
      rw [← EReal.coe_neg, EReal.real_coe_toENNReal, ENNReal.ofReal_eq_zero]
      linarith [hϕ0 y]).trans lintegral_zero
  rw [hzero μ, hzero ν] at hle
  simp only [EReal.coe_ennreal_zero, sub_zero, EReal.real_coe_toENNReal,
    EReal.coe_ennreal_le_coe_ennreal_iff] at hle
  exact hle

/-! ### Section B: Properties of `potential`, asymptotics, and right derivative -/

private lemma potential_convexOn {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    ConvexOn ℝ Set.univ (MartOT.Var.potential μ) := by
  refine ⟨convex_univ, fun x₁ _ x₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, MartOT.Var.potential]
  have h1 : ∀ y : ℝ, |y - (a * x₁ + b * x₂)| ≤ a * |y - x₁| + b * |y - x₂| := fun y => by
    have heq : y - (a * x₁ + b * x₂) = a * (y - x₁) + b * (y - x₂) := by
      calc y - (a * x₁ + b * x₂) = (a + b) * y - (a * x₁ + b * x₂) := by rw [hab, one_mul]
        _ = a * (y - x₁) + b * (y - x₂) := by ring
    rw [heq]
    calc |a * (y - x₁) + b * (y - x₂)|
        ≤ |a * (y - x₁)| + |b * (y - x₂)| := abs_add_le _ _
      _ = a * |y - x₁| + b * |y - x₂| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  calc ∫ y, |y - (a * x₁ + b * x₂)| ∂μ
      ≤ ∫ y, (a * |y - x₁| + b * |y - x₂|) ∂μ :=
        integral_mono (inM_integrable_sub_abs hμ _)
          (((inM_integrable_sub_abs hμ x₁).const_mul a).add
            ((inM_integrable_sub_abs hμ x₂).const_mul b)) h1
    _ = a * ∫ y, |y - x₁| ∂μ + b * ∫ y, |y - x₂| ∂μ := by
        rw [integral_add ((inM_integrable_sub_abs hμ x₁).const_mul a)
          ((inM_integrable_sub_abs hμ x₂).const_mul b),
          integral_const_mul, integral_const_mul]

private lemma potential_add {μ ν : Measure ℝ} (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν)
    (x : ℝ) : MartOT.Var.potential (μ + ν) x = MartOT.Var.potential μ x + MartOT.Var.potential ν x := by
  exact integral_add_measure (inM_integrable_sub_abs hμ x) (inM_integrable_sub_abs hν x)

private lemma potential_sub_eq {μ ν : Measure ℝ} (hle : μ ≤ ν) (hν : MartOT.Var.InM ν) (x : ℝ) :
    MartOT.Var.potential (ν - μ) x = MartOT.Var.potential ν x - MartOT.Var.potential μ x := by
  have hμ := inM_of_le hle hν
  have := hμ.1
  have hsub : MartOT.Var.InM (ν - μ) := inM_of_le Measure.sub_le hν
  have heq : ν - μ + μ = ν := Measure.sub_add_cancel_of_le hle
  have hpot := potential_add hsub hμ x
  rw [heq] at hpot
  linarith

private lemma potential_sub_asymptote_top {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    MartOT.Var.potential μ x - (mass μ * x - mean μ) = 2 * ∫ y, max (y - x) 0 ∂μ := by
  have := hμ.1
  have hsub : Integrable (fun y : ℝ => x - y) μ := (integrable_const x).sub hμ.2
  have hlin : ∫ y, (x - y) ∂μ = mass μ * x - mean μ := by
    rw [integral_sub (integrable_const x) hμ.2, integral_const, smul_eq_mul, Measure.real_def]
    rfl
  rw [← hlin, MartOT.Var.potential, ← integral_sub (inM_integrable_sub_abs hμ x) hsub,
    ← integral_const_mul]
  congr 1; ext y
  rcases le_total y x with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_right (sub_nonpos.mpr h)]; ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left (sub_nonneg.mpr h)]; ring

private lemma potential_sub_asymptote_bot {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    MartOT.Var.potential μ x - (-mass μ * x + mean μ) = 2 * ∫ y, max (x - y) 0 ∂μ := by
  have := hμ.1
  have hsub : Integrable (fun y : ℝ => y - x) μ := hμ.2.sub (integrable_const x)
  have hlin : ∫ y, (y - x) ∂μ = -mass μ * x + mean μ := by
    rw [integral_sub hμ.2 (integrable_const x), integral_const, smul_eq_mul, Measure.real_def]
    unfold mean; ring
  rw [← hlin, MartOT.Var.potential, ← integral_sub (inM_integrable_sub_abs hμ x) hsub,
    ← integral_const_mul]
  congr 1; ext y
  rcases le_total y x with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]; ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]; ring

private lemma potential_tendsto_top {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    Tendsto (fun x => MartOT.Var.potential μ x - (mass μ * x - mean μ)) atTop (𝓝 0) := by
  simp_rw [potential_sub_asymptote_top hμ]
  have hlim : Tendsto (fun x => ∫ y, max (y - x) 0 ∂μ) atTop (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => |y|) ?_ ?_
      (inM_integrable_abs hμ) ?_
    · exact Eventually.of_forall fun x => (inM_integrable_max_sub hμ x).1
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      refine Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self y]) (abs_nonneg y)
    · refine Eventually.of_forall fun y => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop y] with x hx
      exact (max_eq_right (sub_nonpos.mpr hx)).symm
  simpa using hlim.const_mul 2

private lemma potential_tendsto_bot {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    Tendsto (fun x => MartOT.Var.potential μ x - (-mass μ * x + mean μ)) atBot (𝓝 0) := by
  simp_rw [potential_sub_asymptote_bot hμ]
  have hlim : Tendsto (fun x => ∫ y, max (x - y) 0 ∂μ) atBot (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => |y|) ?_ ?_
      (inM_integrable_abs hμ) ?_
    · exact Eventually.of_forall fun x => (inM_integrable_max_sub' hμ x).1
    · filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
      refine Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [neg_le_abs y]) (abs_nonneg y)
    · refine Eventually.of_forall fun y => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_le_atBot y] with x hx
      exact (max_eq_right (sub_nonpos.mpr hx)).symm
  simpa using hlim.const_mul 2

private lemma extConvexLE_potential_lower {μ ν : Measure ℝ} (h : MartOT.Var.ExtConvexLE μ ν)
    (x : ℝ) : |(mass ν - mass μ) * x - (mean ν - mean μ)| ≤
      MartOT.Var.potential ν x - MartOT.Var.potential μ x := by
  have htop : ∫ y, max (y - x) 0 ∂μ ≤ ∫ y, max (y - x) 0 ∂ν := by
    have hle := h.2.2 (fun y => max (y - x) 0) (convexOn_max_sub x) (fun _ => le_max_right _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal (inM_integrable_max_sub h.1 x)
        (Eventually.of_forall fun _ => le_max_right _ _),
      ← ofReal_integral_eq_lintegral_ofReal (inM_integrable_max_sub h.2.1 x)
        (Eventually.of_forall fun _ => le_max_right _ _)] at hle
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => le_max_right _ _)).mp hle
  have hbot : ∫ y, max (x - y) 0 ∂μ ≤ ∫ y, max (x - y) 0 ∂ν := by
    have hle := h.2.2 (fun y => max (x - y) 0) (convexOn_max_sub' x) (fun _ => le_max_right _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal (inM_integrable_max_sub' h.1 x)
        (Eventually.of_forall fun _ => le_max_right _ _),
      ← ofReal_integral_eq_lintegral_ofReal (inM_integrable_max_sub' h.2.1 x)
        (Eventually.of_forall fun _ => le_max_right _ _)] at hle
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => le_max_right _ _)).mp hle
  have ht1 := potential_sub_asymptote_top h.1 x
  have ht2 := potential_sub_asymptote_top h.2.1 x
  have hb1 := potential_sub_asymptote_bot h.1 x
  have hb2 := potential_sub_asymptote_bot h.2.1 x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma potential_hasDerivWithinAt_Ioi {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    HasDerivWithinAt (MartOT.Var.potential μ) (2 * (μ (Iic x)).toReal - mass μ) (Ioi x) x := by
  have := hμ.1
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi]
  have hlim : 2 * (μ (Iic x)).toReal - mass μ =
      ∫ y, ((Iic x).indicator (fun _ => (2 : ℝ)) y - 1) ∂μ := by
    rw [integral_sub ((integrable_const (2 : ℝ)).indicator measurableSet_Iic) (integrable_const 1),
      integral_indicator_const _ measurableSet_Iic, integral_const, smul_eq_mul, smul_eq_mul,
      Measure.real_def, Measure.real_def]
    ring
  rw [hlim]
  have hslope : ∀ᶠ t in 𝓝[>] x,
      slope (MartOT.Var.potential μ) x t = ∫ y, (t - x)⁻¹ * (|y - t| - |y - x|) ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : x < t)
    rw [slope_def_field, MartOT.Var.potential, MartOT.Var.potential,
      ← integral_sub (inM_integrable_sub_abs hμ t) (inM_integrable_sub_abs hμ x),
      div_eq_inv_mul, ← integral_const_mul]
  refine Tendsto.congr' (hslope.mono fun t ht => ht.symm) ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
    (integrable_const 1) ?_
  · exact Eventually.of_forall fun t =>
      (((inM_integrable_sub_abs hμ t).sub (inM_integrable_sub_abs hμ x)).const_mul _).1
  · filter_upwards [self_mem_nhdsWithin] with t (ht : x < t)
    refine Eventually.of_forall fun y => ?_
    have hpos : 0 < t - x := sub_pos.mpr ht
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hpos]
    calc (t - x)⁻¹ * abs (|y - t| - |y - x|)
        ≤ (t - x)⁻¹ * |(y - t) - (y - x)| :=
          mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le _ _) (inv_nonneg.mpr hpos.le)
      _ = (t - x)⁻¹ * |-(t - x)| := by ring_nf
      _ = (t - x)⁻¹ * (t - x) := by rw [abs_neg, abs_of_pos hpos]
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  · refine Eventually.of_forall fun y => ?_
    by_cases hy : y ≤ x
    · have hval : (Iic x).indicator (fun _ => (2 : ℝ)) y - 1 = 1 := by
        rw [Set.indicator_of_mem (mem_Iic.mpr hy)]; norm_num
      rw [hval]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : x < t)
      have hpos : 0 < t - x := sub_pos.mpr ht
      rw [abs_of_nonpos (by linarith : y - t ≤ 0), abs_of_nonpos (by linarith : y - x ≤ 0)]
      have : -(y - t) - -(y - x) = t - x := by ring
      rw [this, inv_mul_cancel₀ hpos.ne']
    · push Not at hy
      have hval : (Iic x).indicator (fun _ => (2 : ℝ)) y - 1 = -1 := by
        rw [Set.indicator_of_notMem (show y ∉ Iic x from not_le.mpr hy)]; norm_num
      rw [hval]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hy] with t ⟨hxt, hty⟩
      have hpos : 0 < t - x := sub_pos.mpr hxt
      rw [abs_of_nonneg (by linarith : 0 ≤ y - t), abs_of_nonneg (by linarith : 0 ≤ y - x)]
      have : (y - t) - (y - x) = -(t - x) := by ring
      rw [this, mul_neg, inv_mul_cancel₀ hpos.ne']

private lemma potential_rderiv_eq {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    rderiv (MartOT.Var.potential μ) x = 2 * (μ (Iic x)).toReal - mass μ :=
  (potential_hasDerivWithinAt_Ioi hμ x).derivWithin (uniqueDiffWithinAt_Ioi x)

private lemma mass_eq_of_potential_eq {μ ν : Measure ℝ} (hμ : MartOT.Var.InM μ)
    (hν : MartOT.Var.InM ν) (heq : ∀ x, MartOT.Var.potential μ x = MartOT.Var.potential ν x) :
    mass μ = mass ν := by
  have hlim : ∀ (m : Measure ℝ), MartOT.Var.InM m →
      Tendsto (fun x : ℝ => MartOT.Var.potential m x / x) atTop (𝓝 (mass m)) := fun m hm => by
    have h1 := (potential_tendsto_top hm).div_atTop tendsto_id
    have h2 : Tendsto (fun x : ℝ => mass m - mean m / x) atTop (𝓝 (mass m)) := by
      simpa using (tendsto_const_nhds (x := mass m)).sub
        ((tendsto_const_nhds (x := mean m)).div_atTop tendsto_id)
    have h3 : Tendsto (fun x : ℝ =>
        (MartOT.Var.potential m x - (mass m * x - mean m)) / x + (mass m - mean m / x))
        atTop (𝓝 (0 + mass m)) := h1.add h2
    rw [zero_add] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
    ring
  have h1 := hlim μ hμ
  have h2 := hlim ν hν
  simp_rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

private lemma measure_eq_of_potential_eq {μ ν : Measure ℝ} (hμ : MartOT.Var.InM μ)
    (hν : MartOT.Var.InM ν) (heq : ∀ x, MartOT.Var.potential μ x = MartOT.Var.potential ν x) :
    μ = ν := by
  have := hμ.1
  have := hν.1
  have hmass := mass_eq_of_potential_eq hμ hν heq
  refine Measure.ext_of_Iic μ ν fun x => ?_
  have hr : rderiv (MartOT.Var.potential μ) x = rderiv (MartOT.Var.potential ν) x := by
    have hfun : MartOT.Var.potential μ = MartOT.Var.potential ν := funext heq
    rw [hfun]
  rw [potential_rderiv_eq hμ x, potential_rderiv_eq hν x, hmass] at hr
  have htr : (μ (Iic x)).toReal = (ν (Iic x)).toReal := by linarith
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp htr

private lemma measure_add_of_potential_add {μ₁ μ₂ ν : Measure ℝ}
    (h1 : MartOT.Var.InM μ₁) (h2 : MartOT.Var.InM μ₂) (hν : MartOT.Var.InM ν)
    (heq : ∀ x, MartOT.Var.potential μ₁ x + MartOT.Var.potential μ₂ x = MartOT.Var.potential ν x) :
    μ₁ + μ₂ = ν :=
  measure_eq_of_potential_eq (inM_add h1 h2) hν fun x => by
    rw [potential_add h1 h2 x, heq x]

/-! ### Section C: Convex functions, right derivative, Stieltjes measure, Meyer-Tanaka -/

private lemma convex_continuous {k : ℝ → ℝ} (hk : ConvexOn ℝ Set.univ k) : Continuous k := by
  rw [← continuousOn_univ]
  simpa [interior_univ] using hk.continuousOn_interior

private lemma convex_hasDerivWithinAt_rderiv {k : ℝ → ℝ} (hk : ConvexOn ℝ Set.univ k) (x : ℝ) :
    HasDerivWithinAt k (rderiv k x) (Ioi x) x :=
  hk.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)

private lemma convex_rderiv_mono {k : ℝ → ℝ} (hk : ConvexOn ℝ Set.univ k) :
    Monotone (rderiv k) := by
  intro x y hxy
  exact hk.monotoneOn_rightDeriv (by simp) (by simp) hxy

private lemma convex_rderiv_le_slope {k : ℝ → ℝ} (hk : ConvexOn ℝ Set.univ k) {x y : ℝ}
    (hxy : x < y) : rderiv k x ≤ slope k x y :=
  hk.rightDeriv_le_slope_of_mem_interior (by simp) (mem_univ y) hxy

private lemma convex_slope_le_rderiv {k : ℝ → ℝ} (hk : ConvexOn ℝ Set.univ k) {x y : ℝ}
    (hxy : x < y) : slope k x y ≤ rderiv k y :=
  (hk.slope_le_leftDeriv_of_mem_interior (mem_univ x) (by simp) hxy).trans
    (hk.leftDeriv_le_rightDeriv_of_mem_interior (by simp))

private lemma convex_rderiv_right_continuous {k : ℝ → ℝ} (hk : ConvexOn ℝ Set.univ k) (x₀ : ℝ) :
    ContinuousWithinAt (rderiv k) (Ici x₀) x₀ := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hderiv := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp
    (convex_hasDerivWithinAt_rderiv hk x₀)
  have hev : ∀ᶠ y in 𝓝[>] x₀, slope k x₀ y < rderiv k x₀ + ε :=
    hderiv.eventually (gt_mem_nhds (by linarith))
  obtain ⟨y, hy_lt, hy_gt⟩ := (hev.and self_mem_nhdsWithin).exists
  have hcont_slope : ContinuousAt (fun x => (k y - k x) / (y - x)) x₀ := by
    refine ((continuousAt_const.sub (convex_continuous hk).continuousAt).div
      (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr hy_gt.ne'))
  have hval : (k y - k x₀) / (y - x₀) < rderiv k x₀ + ε := by
    simpa [slope_def_field] using hy_lt
  have hev2 : ∀ᶠ x in 𝓝 x₀, (k y - k x) / (y - x) < rderiv k x₀ + ε :=
    hcont_slope.eventually (gt_mem_nhds hval)
  rw [Metric.eventually_nhds_iff] at hev2
  obtain ⟨δ₁, hδ₁, hball⟩ := hev2
  refine ⟨min δ₁ (y - x₀), lt_min hδ₁ (sub_pos.mpr hy_gt), fun x hx hdist => ?_⟩
  rw [Real.dist_eq] at hdist ⊢
  have hx_ge : x₀ ≤ x := hx
  have hx_lt_y : x < y := by
    have : x - x₀ < y - x₀ := (abs_lt.mp (hdist.trans_le (min_le_right _ _))).2
    linarith
  have hlow : rderiv k x₀ ≤ rderiv k x := convex_rderiv_mono hk hx_ge
  have hhigh : rderiv k x < rderiv k x₀ + ε := by
    calc rderiv k x ≤ slope k x y := convex_rderiv_le_slope hk hx_lt_y
      _ = (k y - k x) / (y - x) := slope_def_field k x y
      _ < rderiv k x₀ + ε := hball (by rw [Real.dist_eq]; exact hdist.trans_le (min_le_left _ _))
  rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
  linarith

private lemma convex_integral_rderiv {k : ℝ → ℝ} (hk : ConvexOn ℝ Set.univ k) {a b : ℝ}
    (hab : a ≤ b) : ∫ t in a..b, rderiv k t = k b - k a :=
  intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (convex_continuous hk).continuousOn
    (fun t _ => convex_hasDerivWithinAt_rderiv hk t)
    (convex_rderiv_mono hk).intervalIntegrable

private lemma convex_rderiv_asymptotics {k : ℝ → ℝ} (hk : ConvexOn ℝ Set.univ k) {M B : ℝ}
    (htop : Tendsto (fun x => k x - (M * x - B)) atTop (𝓝 0))
    (hbot : Tendsto (fun x => k x - (-M * x + B)) atBot (𝓝 0)) :
    (∀ x, rderiv k x ≤ M) ∧ Tendsto (rderiv k) atTop (𝓝 M) ∧
    (∀ x, -M ≤ rderiv k x) ∧ Tendsto (rderiv k) atBot (𝓝 (-M)) ∧ 0 ≤ M := by
  have hslope_top : ∀ x : ℝ, Tendsto (fun y => slope k x y) atTop (𝓝 M) := fun x => by
    have h1 : Tendsto (fun y : ℝ => (k y - (M * y - B)) / (y - x)) atTop (𝓝 0) :=
      htop.div_atTop (tendsto_id.atTop_add tendsto_const_nhds)
    have h2 : Tendsto (fun y : ℝ => (M * x - B - k x) / (y - x)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.atTop_add tendsto_const_nhds)
    have h3 : Tendsto (fun y : ℝ =>
        M + (k y - (M * y - B)) / (y - x) + (M * x - B - k x) / (y - x))
        atTop (𝓝 (M + 0 + 0)) := (tendsto_const_nhds.add h1).add h2
    simp only [add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop x] with y hy
    have hne : y - x ≠ 0 := (sub_pos.mpr hy).ne'
    rw [slope_def_field]
    field_simp [hne]
    ring
  have hslope_bot : ∀ y : ℝ, Tendsto (fun x => slope k x y) atBot (𝓝 (-M)) := fun y => by
    have hden : Tendsto (fun x : ℝ => y - x) atBot atTop := by
      simpa [sub_eq_add_neg] using
        (tendsto_const_nhds (x := y)).add_atTop tendsto_neg_atBot_atTop
    have h1 : Tendsto (fun x : ℝ => (k x - (-M * x + B)) / (y - x)) atBot (𝓝 0) :=
      hbot.div_atTop hden
    have h2 : Tendsto (fun x : ℝ => (k y - (-M * y + B)) / (y - x)) atBot (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have h3 : Tendsto (fun x : ℝ =>
        -M + (k y - (-M * y + B)) / (y - x) - (k x - (-M * x + B)) / (y - x))
        atBot (𝓝 (-M + 0 - 0)) := (tendsto_const_nhds.add h2).sub h1
    simp only [add_zero, sub_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_lt_atBot y] with x hx
    have hne : y - x ≠ 0 := (sub_pos.mpr hx).ne'
    rw [slope_def_field]
    field_simp [hne]
    ring
  have hle_M : ∀ x, rderiv k x ≤ M := fun x =>
    ge_of_tendsto (hslope_top x) <|
      (eventually_gt_atTop x).mono fun y hy => convex_rderiv_le_slope hk hy
  have hge_negM : ∀ x, -M ≤ rderiv k x := fun x =>
    le_of_tendsto (hslope_bot x) <|
      (eventually_lt_atBot x).mono fun z hz => convex_slope_le_rderiv hk hz
  have ht_top : Tendsto (rderiv k) atTop (𝓝 M) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (hslope_top 0) tendsto_const_nhds
      ((eventually_gt_atTop (0 : ℝ)).mono fun y hy => convex_slope_le_rderiv hk hy)
      (Eventually.of_forall hle_M)
  have ht_bot : Tendsto (rderiv k) atBot (𝓝 (-M)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hslope_bot 0)
      (Eventually.of_forall hge_negM)
      ((eventually_lt_atBot (0 : ℝ)).mono fun x hx => convex_rderiv_le_slope hk hx)
  have hM0 : 0 ≤ M := by linarith [hle_M 0, hge_negM 0]
  exact ⟨hle_M, ht_top, hge_negM, ht_bot, hM0⟩

private lemma convex_stieltjes_exists {k : ℝ → ℝ} (hk : ConvexOn ℝ Set.univ k) {M B : ℝ}
    (htop : Tendsto (fun x => k x - (M * x - B)) atTop (𝓝 0))
    (hbot : Tendsto (fun x => k x - (-M * x + B)) atBot (𝓝 0)) :
    ∃ θ : Measure ℝ, MartOT.Var.InM θ ∧ mass θ = M ∧ mean θ = B ∧
      ∀ x, MartOT.Var.potential θ x = k x := by
  obtain ⟨hle_M, ht_top, hge_negM, ht_bot, hM0⟩ := convex_rderiv_asymptotics hk htop hbot
  let F : StieltjesFunction ℝ :=
    { toFun := fun x => (rderiv k x + M) / 2
      mono' := fun a b hab => div_le_div_of_nonneg_right
        (add_le_add_left (convex_rderiv_mono hk hab) M) (by norm_num)
      right_continuous' := fun x =>
        ((convex_rderiv_right_continuous hk x).add continuousWithinAt_const).div_const 2 }
  have hF_bot : Tendsto F atBot (𝓝 0) := by
    have : (0 : ℝ) = (-M + M) / 2 := by ring
    rw [this]
    exact (ht_bot.add tendsto_const_nhds).div_const 2
  have hF_top : Tendsto F atTop (𝓝 M) := by
    have : M = (M + M) / 2 := by ring
    rw [this]
    exact (ht_top.add tendsto_const_nhds).div_const 2
  let θ : Measure ℝ := F.measure
  have : IsFiniteMeasure θ := F.isFiniteMeasure hF_bot hF_top
  have hθ_univ : θ Set.univ = ENNReal.ofReal M := by
    simpa [θ] using F.measure_univ hF_bot hF_top
  have hθ_mass : mass θ = M := by
    rw [mass, hθ_univ, ENNReal.toReal_ofReal hM0]
  have hθ_Iic : ∀ t, θ (Iic t) = ENNReal.ofReal ((rderiv k t + M) / 2) := fun t => by
    simpa [θ, F] using F.measure_Iic hF_bot t
  have hθ_Ioi : ∀ t, θ (Ioi t) = ENNReal.ofReal ((M - rderiv k t) / 2) := fun t => by
    have h := F.measure_Ioi hF_top t
    have heq : M - (rderiv k t + M) / 2 = (M - rderiv k t) / 2 := by ring
    simpa [θ, F, heq] using h
  -- Compute lintegral of max (y - x) 0 and max (x - y) 0 for any x
  have hpos_lint : ∀ x : ℝ,
      ∫⁻ y, ENNReal.ofReal (max (y - x) 0) ∂θ = ENNReal.ofReal ((k x - M * x + B) / 2) ∧
      0 ≤ (k x - M * x + B) / 2 := fun x => by
    let g : ℝ → ℝ → ENNReal :=
      fun y t => ({p : ℝ × ℝ | x < p.2 ∧ p.2 < p.1}).indicator (fun _ => (1 : ENNReal)) (y, t)
    have hg_meas : Measurable (Function.uncurry g) :=
      measurable_const.indicator
        ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
          (isOpen_lt continuous_snd continuous_fst).measurableSet)
    have hswap := lintegral_lintegral_swap (μ := θ) (ν := volume) hg_meas.aemeasurable
    have hlhs : (∫⁻ y, ∫⁻ t, g y t ∂volume ∂θ) = ∫⁻ y, ENNReal.ofReal (max (y - x) 0) ∂θ := by
      congr 1; ext y
      have hset : (fun t => g y t) = (Ioo x y).indicator (fun _ => (1 : ENNReal)) := by
        ext t; simp [g, Set.indicator, Set.mem_Ioo]
      rw [hset, lintegral_indicator measurableSet_Ioo, setLIntegral_one, Real.volume_Ioo]
      rcases le_total y x with h | h
      · rw [max_eq_right (sub_nonpos.mpr h), ENNReal.ofReal_of_nonpos (sub_nonpos.mpr h),
          ENNReal.ofReal_zero]
      · rw [max_eq_left (sub_nonneg.mpr h)]
    have hrhs : (∫⁻ t, ∫⁻ y, g y t ∂θ ∂volume) = ∫⁻ t in Ioi x, θ (Ioi t) ∂volume := by
      rw [← lintegral_indicator measurableSet_Ioi]
      congr 1; ext t
      by_cases hxt : x < t
      · rw [Set.indicator_of_mem (mem_Ioi.mpr hxt)]
        have hset : (fun y => g y t) = (Ioi t).indicator (fun _ => (1 : ENNReal)) := by
          ext y; simp [g, Set.indicator, hxt]
        rw [hset, lintegral_indicator measurableSet_Ioi, setLIntegral_one]
      · rw [Set.indicator_of_notMem (show t ∉ Ioi x from hxt)]
        have hzero : ∀ y, g y t = 0 := fun y => by simp [g, Set.indicator, hxt]
        simp [hzero]
    rw [hlhs, hrhs] at hswap
    have hunion : Ioi x = ⋃ n : ℕ, Ioc x (x + (n : ℝ)) := by
      ext t; simp only [mem_Ioi, mem_iUnion, mem_Ioc]
      constructor
      · intro hxt
        obtain ⟨n, hn⟩ := exists_nat_gt (t - x)
        exact ⟨n, hxt, by linarith⟩
      · rintro ⟨_, hxt, _⟩; exact hxt
    have hdir : Directed (· ⊆ ·) (fun n : ℕ => Ioc x (x + (n : ℝ))) :=
      (Monotone.directed_le fun a b hab => Ioc_subset_Ioc_right (by gcongr))
    rw [hunion, setLIntegral_iUnion_of_directed _ hdir] at hswap
    have hterm : ∀ n : ℕ, ∫⁻ t in Ioc x (x + (n : ℝ)), θ (Ioi t) ∂volume =
        ENNReal.ofReal ((k x - M * x + B - (k (x + n) - (M * (x + n) - B))) / 2) := fun n => by
      simp_rw [hθ_Ioi]
      have hle : x ≤ x + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
      have hint : IntervalIntegrable (fun t => (M - rderiv k t) / 2) volume x (x + n) :=
        ((intervalIntegrable_const.sub (convex_rderiv_mono hk).intervalIntegrable).div_const 2)
      rw [← ofReal_integral_eq_lintegral_ofReal
          (intervalIntegrable_iff_integrableOn_Ioc_of_le hle |>.mp hint)
          (Eventually.of_forall fun t => div_nonneg (sub_nonneg.mpr (hle_M t)) (by norm_num))]
      rw [← intervalIntegral.integral_of_le hle]
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_sub intervalIntegrable_const
          (convex_rderiv_mono hk).intervalIntegrable,
        intervalIntegral.integral_const, smul_eq_mul, convex_integral_rderiv hk hle]
      congr 1; ring
    simp_rw [hterm] at hswap
    have hseq_nonneg : ∀ n : ℕ, 0 ≤ (k x - M * x + B - (k (x + n) - (M * (x + n) - B))) / 2 :=
      fun n => by
        have hle : x ≤ x + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
        have : (k x - M * x + B - (k (x + n) - (M * (x + n) - B))) / 2 =
            ∫ t in x..(x + n), (M - rderiv k t) / 2 := by
          rw [intervalIntegral.integral_div,
            intervalIntegral.integral_sub intervalIntegrable_const
              (convex_rderiv_mono hk).intervalIntegrable,
            intervalIntegral.integral_const, smul_eq_mul, convex_integral_rderiv hk hle]; ring
        rw [this]
        exact intervalIntegral.integral_nonneg hle fun t _ =>
          div_nonneg (sub_nonneg.mpr (hle_M t)) (by norm_num)
    have hseq_tendsto : Tendsto
        (fun n : ℕ => (k x - M * x + B - (k (x + n) - (M * (x + n) - B))) / 2)
        atTop (𝓝 ((k x - M * x + B) / 2)) := by
      have ht1 : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop :=
        (tendsto_const_nhds (x := x)).add_atTop tendsto_natCast_atTop_atTop
      have ht2 := htop.comp ht1
      have : (k x - M * x + B) / 2 = (k x - M * x + B - 0) / 2 := by ring
      rw [this]
      exact (tendsto_const_nhds.sub ht2).div_const 2
    have hnn : 0 ≤ (k x - M * x + B) / 2 := ge_of_tendsto hseq_tendsto (Eventually.of_forall hseq_nonneg)
    have hmono : Monotone (fun n : ℕ =>
        ENNReal.ofReal ((k x - M * x + B - (k (x + n) - (M * (x + n) - B))) / 2)) := by
      intro a b hab
      dsimp only
      rw [← hterm a, ← hterm b]
      exact lintegral_mono_set (Ioc_subset_Ioc_right (by gcongr))
    have hsup_eq : (⨆ n : ℕ,
        ENNReal.ofReal ((k x - M * x + B - (k (x + n) - (M * (x + n) - B))) / 2)) =
        ENNReal.ofReal ((k x - M * x + B) / 2) :=
      tendsto_nhds_unique (tendsto_atTop_iSup hmono) (ENNReal.tendsto_ofReal hseq_tendsto)
    exact ⟨hswap.trans hsup_eq, hnn⟩
  have hneg_lint : ∀ x : ℝ,
      ∫⁻ y, ENNReal.ofReal (max (x - y) 0) ∂θ = ENNReal.ofReal ((k x + M * x - B) / 2) ∧
      0 ≤ (k x + M * x - B) / 2 := fun x => by
    let g : ℝ → ℝ → ENNReal :=
      fun y t => ({p : ℝ × ℝ | p.1 ≤ p.2 ∧ p.2 ≤ x}).indicator (fun _ => (1 : ENNReal)) (y, t)
    have hg_meas : Measurable (Function.uncurry g) :=
      measurable_const.indicator
        ((isClosed_le continuous_fst continuous_snd).measurableSet.inter
          (isClosed_le continuous_snd continuous_const).measurableSet)
    have hswap := lintegral_lintegral_swap (μ := θ) (ν := volume) hg_meas.aemeasurable
    have hlhs : (∫⁻ y, ∫⁻ t, g y t ∂volume ∂θ) = ∫⁻ y, ENNReal.ofReal (max (x - y) 0) ∂θ := by
      congr 1; ext y
      have hset : (fun t => g y t) = (Icc y x).indicator (fun _ => (1 : ENNReal)) := by
        ext t; simp [g, Set.indicator, Set.mem_Icc]
      rw [hset, lintegral_indicator measurableSet_Icc, setLIntegral_one, Real.volume_Icc]
      rcases le_total y x with h | h
      · rw [max_eq_left (sub_nonneg.mpr h)]
      · rw [max_eq_right (sub_nonpos.mpr h), ENNReal.ofReal_of_nonpos (sub_nonpos.mpr h),
          ENNReal.ofReal_zero]
    have hrhs : (∫⁻ t, ∫⁻ y, g y t ∂θ ∂volume) = ∫⁻ t in Iic x, θ (Iic t) ∂volume := by
      rw [← lintegral_indicator measurableSet_Iic]
      congr 1; ext t
      by_cases htx : t ≤ x
      · rw [Set.indicator_of_mem (mem_Iic.mpr htx)]
        have hset : (fun y => g y t) = (Iic t).indicator (fun _ => (1 : ENNReal)) := by
          ext y; simp [g, Set.indicator, htx]
        rw [hset, lintegral_indicator measurableSet_Iic, setLIntegral_one]
      · rw [Set.indicator_of_notMem (show t ∉ Iic x from htx)]
        have hzero : ∀ y, g y t = 0 := fun y => by simp [g, Set.indicator, htx]
        simp [hzero]
    rw [hlhs, hrhs] at hswap
    have hunion : Iic x = ⋃ n : ℕ, Ioc (x - ((n + 1 : ℕ) : ℝ)) x := by
      ext t; simp only [mem_Iic, mem_iUnion, mem_Ioc]
      constructor
      · intro htx
        obtain ⟨n, hn⟩ := exists_nat_gt (x - t)
        exact ⟨n, by push_cast; linarith, htx⟩
      · rintro ⟨_, _, htx⟩; exact htx
    have hdir : Directed (· ⊆ ·) (fun n : ℕ => Ioc (x - ((n + 1 : ℕ) : ℝ)) x) :=
      (Monotone.directed_le fun a b hab => Ioc_subset_Ioc_left (by gcongr))
    rw [hunion, setLIntegral_iUnion_of_directed _ hdir] at hswap
    have hterm : ∀ n : ℕ, ∫⁻ t in Ioc (x - ((n + 1 : ℕ) : ℝ)) x, θ (Iic t) ∂volume =
        ENNReal.ofReal ((k x + M * x - B -
          (k (x - ((n + 1 : ℕ) : ℝ)) - (-M * (x - ((n + 1 : ℕ) : ℝ)) + B))) / 2) := fun n => by
      simp_rw [hθ_Iic]
      have hle : x - ((n + 1 : ℕ) : ℝ) ≤ x := sub_le_self x (Nat.cast_nonneg _)
      have hint : IntervalIntegrable (fun t => (rderiv k t + M) / 2) volume
          (x - ((n + 1 : ℕ) : ℝ)) x :=
        (((convex_rderiv_mono hk).intervalIntegrable.add intervalIntegrable_const).div_const 2)
      rw [← ofReal_integral_eq_lintegral_ofReal
          (intervalIntegrable_iff_integrableOn_Ioc_of_le hle |>.mp hint)
          (Eventually.of_forall fun t => div_nonneg (by linarith [hge_negM t]) (by norm_num))]
      rw [← intervalIntegral.integral_of_le hle]
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_add (convex_rderiv_mono hk).intervalIntegrable
          intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, convex_integral_rderiv hk hle]
      congr 1; ring
    simp_rw [hterm] at hswap
    have hseq_nonneg : ∀ n : ℕ, 0 ≤ (k x + M * x - B -
        (k (x - ((n + 1 : ℕ) : ℝ)) - (-M * (x - ((n + 1 : ℕ) : ℝ)) + B))) / 2 := fun n => by
      have hle : x - ((n + 1 : ℕ) : ℝ) ≤ x := sub_le_self x (Nat.cast_nonneg _)
      have : (k x + M * x - B -
          (k (x - ((n + 1 : ℕ) : ℝ)) - (-M * (x - ((n + 1 : ℕ) : ℝ)) + B))) / 2 =
          ∫ t in (x - ((n + 1 : ℕ) : ℝ))..x, (rderiv k t + M) / 2 := by
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_add (convex_rderiv_mono hk).intervalIntegrable
            intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul, convex_integral_rderiv hk hle]; ring
      rw [this]
      exact intervalIntegral.integral_nonneg hle fun t _ =>
        div_nonneg (by linarith [hge_negM t]) (by norm_num)
    have hseq_tendsto : Tendsto
        (fun n : ℕ => (k x + M * x - B -
          (k (x - ((n + 1 : ℕ) : ℝ)) - (-M * (x - ((n + 1 : ℕ) : ℝ)) + B))) / 2)
        atTop (𝓝 ((k x + M * x - B) / 2)) := by
      have ht1 : Tendsto (fun n : ℕ => x - ((n + 1 : ℕ) : ℝ)) atTop atBot := by
        have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
        simpa [sub_eq_add_neg] using
          (tendsto_const_nhds (x := x)).add_atBot (tendsto_neg_atTop_atBot.comp hnat)
      have ht2 := hbot.comp ht1
      have : (k x + M * x - B) / 2 = (k x + M * x - B - 0) / 2 := by ring
      rw [this]
      exact (tendsto_const_nhds.sub ht2).div_const 2
    have hnn : 0 ≤ (k x + M * x - B) / 2 := ge_of_tendsto hseq_tendsto (Eventually.of_forall hseq_nonneg)
    have hmono : Monotone (fun n : ℕ => ENNReal.ofReal ((k x + M * x - B -
        (k (x - ((n + 1 : ℕ) : ℝ)) - (-M * (x - ((n + 1 : ℕ) : ℝ)) + B))) / 2)) := by
      intro a b hab
      dsimp only
      rw [← hterm a, ← hterm b]
      exact lintegral_mono_set (Ioc_subset_Ioc_left (by gcongr))
    have hsup_eq : (⨆ n : ℕ, ENNReal.ofReal ((k x + M * x - B -
        (k (x - ((n + 1 : ℕ) : ℝ)) - (-M * (x - ((n + 1 : ℕ) : ℝ)) + B))) / 2)) =
        ENNReal.ofReal ((k x + M * x - B) / 2) :=
      tendsto_nhds_unique (tendsto_atTop_iSup hmono) (ENNReal.tendsto_ofReal hseq_tendsto)
    exact ⟨hswap.trans hsup_eq, hnn⟩
  -- Deduce InM θ, mean θ = B, and potential θ = k
  have hθ_int : Integrable (fun y : ℝ => y) θ := by
    refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
    show ∫⁻ y, ‖y‖ₑ ∂θ < ⊤
    have hle : (∫⁻ y, ‖y‖ₑ ∂θ) ≤
        (∫⁻ y, ENNReal.ofReal (max (y - 0) 0) ∂θ) + ∫⁻ y, ENNReal.ofReal (max (0 - y) 0) ∂θ := by
      calc ∫⁻ y, ‖y‖ₑ ∂θ
          ≤ ∫⁻ y, (ENNReal.ofReal (max (y - 0) 0) + ENNReal.ofReal (max (0 - y) 0)) ∂θ :=
            lintegral_mono fun y => by
              rw [Real.enorm_eq_ofReal_abs,
                ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
              exact ENNReal.ofReal_le_ofReal (by
                rcases le_total y 0 with h | h
                · rw [abs_of_nonpos h, max_eq_right (by linarith), max_eq_left (by linarith)]
                  linarith
                · rw [abs_of_nonneg h, max_eq_left (by linarith), max_eq_right (by linarith)]
                  linarith)
        _ = (∫⁻ y, ENNReal.ofReal (max (y - 0) 0) ∂θ) +
            ∫⁻ y, ENNReal.ofReal (max (0 - y) 0) ∂θ :=
            lintegral_add_left
              (ENNReal.measurable_ofReal.comp
                ((measurable_id.sub measurable_const).max measurable_const)) _
    refine lt_of_le_of_lt hle ?_
    rw [(hpos_lint 0).1, (hneg_lint 0).1]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  have hθ_inM : MartOT.Var.InM θ := ⟨inferInstance, hθ_int⟩
  have hpos_int : ∀ x, ∫ y, max (y - x) 0 ∂θ = (k x - M * x + B) / 2 := fun x => by
    have h := (hpos_lint x).1
    rw [← ofReal_integral_eq_lintegral_ofReal (inM_integrable_max_sub hθ_inM x)
      (Eventually.of_forall fun _ => le_max_right _ _)] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => le_max_right _ _)
      (hpos_lint x).2).mp h
  have hneg_int : ∀ x, ∫ y, max (x - y) 0 ∂θ = (k x + M * x - B) / 2 := fun x => by
    have h := (hneg_lint x).1
    rw [← ofReal_integral_eq_lintegral_ofReal (inM_integrable_max_sub' hθ_inM x)
      (Eventually.of_forall fun _ => le_max_right _ _)] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => le_max_right _ _)
      (hneg_lint x).2).mp h
  have hθ_mean : mean θ = B := by
    have heq : (fun y : ℝ => y) = fun y => max (y - 0) 0 - max (0 - y) 0 := by
      ext y; rcases le_total y 0 with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; linarith
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    rw [mean, heq, integral_sub (inM_integrable_max_sub hθ_inM 0) (inM_integrable_max_sub' hθ_inM 0),
      hpos_int 0, hneg_int 0]
    ring
  have hθ_pot : ∀ x, MartOT.Var.potential θ x = k x := fun x => by
    have heq : (fun y : ℝ => |y - x|) = fun y => max (y - x) 0 + max (x - y) 0 := by
      ext y; rcases le_total y x with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_right (sub_nonpos.mpr h),
          max_eq_left (sub_nonneg.mpr h)]; ring
      · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left (sub_nonneg.mpr h),
          max_eq_right (sub_nonpos.mpr h)]; ring
    rw [MartOT.Var.potential, heq,
      integral_add (inM_integrable_max_sub hθ_inM x) (inM_integrable_max_sub' hθ_inM x),
      hpos_int x, hneg_int x]
    ring
  exact ⟨θ, hθ_inM, hθ_mass, hθ_mean, hθ_pot⟩

private lemma convexLE_of_potential_le {μ ν : Measure ℝ}
    (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν)
    (hmass : mass μ = mass ν) (hmean : mean μ = mean ν)
    (hpot : ∀ x, MartOT.Var.potential μ x ≤ MartOT.Var.potential ν x) :
    MartOT.Var.ConvexLE μ ν := by
  have := hμ.1
  have := hν.1
  refine ⟨hμ, hν, fun ϕ hϕ => ?_⟩
  let S : StieltjesFunction ℝ :=
    { toFun := rderiv ϕ
      mono' := convex_rderiv_mono hϕ
      right_continuous' := convex_rderiv_right_continuous hϕ }
  let σ : Measure ℝ := S.measure
  let a : ℝ → ℝ := fun x => ϕ 0 + rderiv ϕ 0 * x
  let ψ : ℝ → ℝ := fun x => ϕ x - a x
  have hψ_nonneg : ∀ x, 0 ≤ ψ x := fun x => by
    simp only [ψ, a]
    rcases lt_trichotomy 0 x with h | rfl | h
    · have := convex_rderiv_le_slope hϕ h
      rw [slope_def_field, sub_zero, le_div_iff₀ h] at this; linarith
    · linarith
    · have := convex_slope_le_rderiv hϕ h
      rw [slope_def_field, zero_sub, div_le_iff₀ (neg_pos.mpr h)] at this
      linarith
  have hψ_meas : Measurable ψ :=
    ((convex_continuous hϕ).sub (continuous_const.add (continuous_const.mul continuous_id))).measurable
  -- Meyer-Tanaka identity
  have hMT : ∀ x : ℝ, ENNReal.ofReal (ψ x) =
      (∫⁻ t in Ioi 0, ENNReal.ofReal (max (x - t) 0) ∂σ) +
      (∫⁻ t in Iic 0, ENNReal.ofReal (max (t - x) 0) ∂σ) := fun x => by
    by_cases hx : 0 ≤ x
    · have h2 : ∫⁻ t in Iic 0, ENNReal.ofReal (max (t - x) 0) ∂σ = 0 := by
        refine setLIntegral_eq_zero measurableSet_Iic fun t ht => ?_
        rw [max_eq_right (by linarith [show t ≤ 0 from ht]), ENNReal.ofReal_zero]; rfl
      rw [h2, add_zero]
      let g : ℝ → ℝ → ENNReal :=
        fun t s => ({p : ℝ × ℝ | 0 < p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ x}).indicator
          (fun _ => (1 : ENNReal)) (t, s)
      have hg_meas : Measurable (Function.uncurry g) :=
        measurable_const.indicator
          ((isOpen_lt continuous_const continuous_fst).measurableSet.inter
            ((isClosed_le continuous_fst continuous_snd).measurableSet.inter
              (isClosed_le continuous_snd continuous_const).measurableSet))
      have hswap := lintegral_lintegral_swap (μ := σ) (ν := volume) hg_meas.aemeasurable
      have hlhs : (∫⁻ t, ∫⁻ s, g t s ∂volume ∂σ) =
          ∫⁻ t in Ioi 0, ENNReal.ofReal (max (x - t) 0) ∂σ := by
        rw [← lintegral_indicator measurableSet_Ioi]
        congr 1; ext t
        by_cases ht : 0 < t
        · rw [Set.indicator_of_mem (mem_Ioi.mpr ht)]
          have hset : (fun s => g t s) = (Icc t x).indicator (fun _ => (1 : ENNReal)) := by
            ext s; simp [g, Set.indicator, ht, Set.mem_Icc]
          rw [hset, lintegral_indicator measurableSet_Icc, setLIntegral_one, Real.volume_Icc]
          rcases le_total t x with htx | htx
          · rw [max_eq_left (sub_nonneg.mpr htx)]
          · rw [max_eq_right (sub_nonpos.mpr htx), ENNReal.ofReal_of_nonpos (sub_nonpos.mpr htx),
              ENNReal.ofReal_zero]
        · rw [Set.indicator_of_notMem (show t ∉ Ioi 0 from ht)]
          have hzero : ∀ s, g t s = 0 := fun s => by simp [g, Set.indicator, ht]
          simp [hzero]
      have hrhs : (∫⁻ s, ∫⁻ t, g t s ∂σ ∂volume) = ENNReal.ofReal (ψ x) := by
        have hstep : (∫⁻ s, ∫⁻ t, g t s ∂σ ∂volume) =
            ∫⁻ s in Ioc 0 x, ENNReal.ofReal (rderiv ϕ s - rderiv ϕ 0) ∂volume := by
          rw [← lintegral_indicator measurableSet_Ioc]
          congr 1; ext s
          by_cases hs : s ∈ Ioc 0 x
          · rw [Set.indicator_of_mem hs]
            have hset : (fun t => g t s) = (Ioc 0 s).indicator (fun _ => (1 : ENNReal)) := by
              ext t; simp [g, Set.indicator, hs.2, Set.mem_Ioc]
            rw [hset, lintegral_indicator measurableSet_Ioc, setLIntegral_one]
            exact S.measure_Ioc 0 s
          · rw [Set.indicator_of_notMem hs]
            have hzero : ∀ t, g t s = 0 := fun t => by
              simp only [g, Set.indicator, mem_ofPred_eq, ite_eq_right_iff]
              rintro ⟨h0t, hts, hsx⟩
              exact (hs ⟨h0t.trans_le hts, hsx⟩).elim
            simp [hzero]
        rw [hstep]
        have hint : IntervalIntegrable (fun s => rderiv ϕ s - rderiv ϕ 0) volume 0 x :=
          (convex_rderiv_mono hϕ).intervalIntegrable.sub intervalIntegrable_const
        rw [← ofReal_integral_eq_lintegral_ofReal
            (intervalIntegrable_iff_integrableOn_Ioc_of_le hx |>.mp hint)
            (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
              sub_nonneg.mpr (convex_rderiv_mono hϕ hs.1.le))]
        rw [← intervalIntegral.integral_of_le hx,
          intervalIntegral.integral_sub (convex_rderiv_mono hϕ).intervalIntegrable
            intervalIntegrable_const,
          convex_integral_rderiv hϕ hx, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        congr 1; simp only [ψ, a]; ring
      rw [← hrhs, ← hswap, hlhs]
    · push Not at hx
      have h1 : ∫⁻ t in Ioi 0, ENNReal.ofReal (max (x - t) 0) ∂σ = 0 := by
        refine setLIntegral_eq_zero measurableSet_Ioi fun t ht => ?_
        rw [max_eq_right (by linarith [show 0 < t from ht]), ENNReal.ofReal_zero]; rfl
      rw [h1, zero_add]
      let g : ℝ → ℝ → ENNReal :=
        fun t s => ({p : ℝ × ℝ | x < p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 0}).indicator
          (fun _ => (1 : ENNReal)) (t, s)
      have hg_meas : Measurable (Function.uncurry g) :=
        measurable_const.indicator
          ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
            ((isOpen_lt continuous_snd continuous_fst).measurableSet.inter
              (isClosed_le continuous_fst continuous_const).measurableSet))
      have hswap := lintegral_lintegral_swap (μ := σ) (ν := volume) hg_meas.aemeasurable
      have hlhs : (∫⁻ t, ∫⁻ s, g t s ∂volume ∂σ) =
          ∫⁻ t in Iic 0, ENNReal.ofReal (max (t - x) 0) ∂σ := by
        rw [← lintegral_indicator measurableSet_Iic]
        congr 1; ext t
        by_cases ht : t ≤ 0
        · rw [Set.indicator_of_mem (mem_Iic.mpr ht)]
          have hset : (fun s => g t s) = (Ioo x t).indicator (fun _ => (1 : ENNReal)) := by
            ext s; simp [g, Set.indicator, ht, Set.mem_Ioo]
          rw [hset, lintegral_indicator measurableSet_Ioo, setLIntegral_one, Real.volume_Ioo]
          rcases le_total t x with htx | htx
          · rw [max_eq_right (sub_nonpos.mpr htx), ENNReal.ofReal_of_nonpos (sub_nonpos.mpr htx),
              ENNReal.ofReal_zero]
          · rw [max_eq_left (sub_nonneg.mpr htx)]
        · rw [Set.indicator_of_notMem (show t ∉ Iic 0 from ht)]
          have hzero : ∀ s, g t s = 0 := fun s => by simp [g, Set.indicator, ht]
          simp [hzero]
      have hrhs : (∫⁻ s, ∫⁻ t, g t s ∂σ ∂volume) = ENNReal.ofReal (ψ x) := by
        have hstep : (∫⁻ s, ∫⁻ t, g t s ∂σ ∂volume) =
            ∫⁻ s in Ioc x 0, ENNReal.ofReal (rderiv ϕ 0 - rderiv ϕ s) ∂volume := by
          rw [← lintegral_indicator measurableSet_Ioc]
          congr 1; ext s
          by_cases hs : s ∈ Ioc x 0
          · rw [Set.indicator_of_mem hs]
            have hset : (fun t => g t s) = (Ioc s 0).indicator (fun _ => (1 : ENNReal)) := by
              ext t; simp [g, Set.indicator, hs.1, Set.mem_Ioc]
            rw [hset, lintegral_indicator measurableSet_Ioc, setLIntegral_one]
            exact S.measure_Ioc s 0
          · rw [Set.indicator_of_notMem hs]
            have hzero : ∀ t, g t s = 0 := fun t => by
              simp only [g, Set.indicator, mem_ofPred_eq, ite_eq_right_iff]
              rintro ⟨hxs, hst, ht0⟩
              exact (hs ⟨hxs, hst.le.trans ht0⟩).elim
            simp [hzero]
        rw [hstep]
        have hint : IntervalIntegrable (fun s => rderiv ϕ 0 - rderiv ϕ s) volume x 0 :=
          intervalIntegrable_const.sub (convex_rderiv_mono hϕ).intervalIntegrable
        rw [← ofReal_integral_eq_lintegral_ofReal
            (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le |>.mp hint)
            (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
              sub_nonneg.mpr (convex_rderiv_mono hϕ hs.2))]
        rw [← intervalIntegral.integral_of_le hx.le,
          intervalIntegral.integral_sub intervalIntegrable_const
            (convex_rderiv_mono hϕ).intervalIntegrable,
          convex_integral_rderiv hϕ hx.le, intervalIntegral.integral_const, smul_eq_mul, zero_sub]
        congr 1; simp only [ψ, a]; ring
      rw [← hrhs, ← hswap, hlhs]
  -- Integrate hMT against μ and ν and swap
  have hlint_le : ∫⁻ x, ENNReal.ofReal (ψ x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (ψ x) ∂ν := by
    have hsplit : ∀ (m : Measure ℝ), MartOT.Var.InM m →
        ∫⁻ x, ENNReal.ofReal (ψ x) ∂m =
          (∫⁻ t in Ioi 0, ∫⁻ x, ENNReal.ofReal (max (x - t) 0) ∂m ∂σ) +
          (∫⁻ t in Iic 0, ∫⁻ x, ENNReal.ofReal (max (t - x) 0) ∂m ∂σ) := fun m hm => by
      have := hm.1
      simp_rw [hMT]
      have hm1 : Measurable (fun x : ℝ => ∫⁻ t in Ioi 0, ENNReal.ofReal (max (x - t) 0) ∂σ) :=
        (ENNReal.measurable_ofReal.comp
          ((measurable_fst.sub measurable_snd).max measurable_const)).lintegral_prod_right'
      rw [lintegral_add_left hm1]
      congr 1
      · exact lintegral_lintegral_swap (μ := m) (ν := σ.restrict (Ioi 0))
          (ENNReal.measurable_ofReal.comp
            ((measurable_fst.sub measurable_snd).max measurable_const)).aemeasurable
      · exact lintegral_lintegral_swap (μ := m) (ν := σ.restrict (Iic 0))
          (ENNReal.measurable_ofReal.comp
            ((measurable_snd.sub measurable_fst).max measurable_const)).aemeasurable
    rw [hsplit μ hμ, hsplit ν hν]
    refine add_le_add (setLIntegral_mono' measurableSet_Ioi fun t _ => ?_)
      (setLIntegral_mono' measurableSet_Iic fun t _ => ?_)
    · rw [← ofReal_integral_eq_lintegral_ofReal (inM_integrable_max_sub hμ t)
          (Eventually.of_forall fun _ => le_max_right _ _),
        ← ofReal_integral_eq_lintegral_ofReal (inM_integrable_max_sub hν t)
          (Eventually.of_forall fun _ => le_max_right _ _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := potential_sub_asymptote_top hμ t
      have h2 := potential_sub_asymptote_top hν t
      rw [hmass, hmean] at h1
      linarith [hpot t]
    · rw [← ofReal_integral_eq_lintegral_ofReal (inM_integrable_max_sub' hμ t)
          (Eventually.of_forall fun _ => le_max_right _ _),
        ← ofReal_integral_eq_lintegral_ofReal (inM_integrable_max_sub' hν t)
          (Eventually.of_forall fun _ => le_max_right _ _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := potential_sub_asymptote_bot hμ t
      have h2 := potential_sub_asymptote_bot hν t
      rw [hmass, hmean] at h1
      linarith [hpot t]
  have ha_μ : Integrable a μ := (integrable_const _).add (hμ.2.const_mul _)
  have ha_ν : Integrable a ν := (integrable_const _).add (hν.2.const_mul _)
  have ha_eq : ∫ x, a x ∂μ = ∫ x, a x ∂ν := by
    simp only [a]
    rw [integral_add (integrable_const _) (hμ.2.const_mul _),
      integral_add (integrable_const _) (hν.2.const_mul _),
      integral_const, integral_const, integral_const_mul, integral_const_mul,
      smul_eq_mul, smul_eq_mul, Measure.real_def, Measure.real_def]
    change mass μ * ϕ 0 + rderiv ϕ 0 * mean μ = mass ν * ϕ 0 + rderiv ϕ 0 * mean ν
    rw [hmass, hmean]
  have hϕ_eq : ϕ = fun x => ψ x + a x := by ext x; simp [ψ]
  rw [hϕ_eq, integralE_add_integrable hψ_meas hψ_nonneg ha_μ,
    integralE_add_integrable hψ_meas hψ_nonneg ha_ν, ha_eq]
  exact add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hlint_le) le_rfl

/-! ### Section D: Lower convex envelope `convEnv` and convexity of `v - convEnv (v - u)` -/

private lemma convEnv_bddAbove (f : ℝ → ℝ) (x : ℝ) :
    BddAbove {y : ℝ | ∃ k : ℝ → ℝ, ConvexOn ℝ Set.univ k ∧ (∀ z, k z ≤ f z) ∧ k x = y} :=
  ⟨f x, by rintro _ ⟨k, _, hle, rfl⟩; exact hle x⟩

private lemma convEnv_nonempty {f L : ℝ → ℝ} (hL : ConvexOn ℝ Set.univ L) (hLf : ∀ z, L z ≤ f z)
    (x : ℝ) :
    {y : ℝ | ∃ k : ℝ → ℝ, ConvexOn ℝ Set.univ k ∧ (∀ z, k z ≤ f z) ∧ k x = y}.Nonempty :=
  ⟨L x, L, hL, hLf, rfl⟩

private lemma convEnv_le {f L : ℝ → ℝ} (hL : ConvexOn ℝ Set.univ L) (hLf : ∀ z, L z ≤ f z)
    (x : ℝ) : convEnv f x ≤ f x :=
  csSup_le (convEnv_nonempty hL hLf x) (by rintro _ ⟨k, _, hle, rfl⟩; exact hle x)

private lemma le_convEnv {f k : ℝ → ℝ} (hk : ConvexOn ℝ Set.univ k) (hkf : ∀ z, k z ≤ f z)
    (x : ℝ) : k x ≤ convEnv f x :=
  le_csSup (convEnv_bddAbove f x) ⟨k, hk, hkf, rfl⟩

private lemma convEnv_convexOn {f L : ℝ → ℝ} (hL : ConvexOn ℝ Set.univ L) (hLf : ∀ z, L z ≤ f z) :
    ConvexOn ℝ Set.univ (convEnv f) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  refine csSup_le (convEnv_nonempty hL hLf _) ?_
  rintro _ ⟨k, hk, hkf, rfl⟩
  calc k (a * x + b * y)
      ≤ a * k x + b * k y := by simpa [smul_eq_mul] using hk.2 (mem_univ x) (mem_univ y) ha hb hab
    _ ≤ a * convEnv f x + b * convEnv f y :=
        add_le_add (mul_le_mul_of_nonneg_left (le_convEnv hk hkf x) ha)
          (mul_le_mul_of_nonneg_left (le_convEnv hk hkf y) hb)

private lemma convEnv_sub_convex {f u L : ℝ → ℝ} (hu : ConvexOn ℝ Set.univ u)
    (hL : ConvexOn ℝ Set.univ L) (hLf : ∀ z, L z ≤ f z - u z) :
    ∀ x, convEnv (fun z => f z - u z) x = convEnv (fun z => convEnv f z - u z) x := fun x => by
  have hLf' : ∀ z, L z + u z ≤ f z := fun z => by linarith [hLf z]
  show sSup {y : ℝ | ∃ k : ℝ → ℝ, ConvexOn ℝ Set.univ k ∧ (∀ z, k z ≤ f z - u z) ∧ k x = y} =
    sSup {y : ℝ | ∃ k : ℝ → ℝ, ConvexOn ℝ Set.univ k ∧ (∀ z, k z ≤ convEnv f z - u z) ∧ k x = y}
  congr 1; ext y; constructor
  · rintro ⟨k, hk, hkf, rfl⟩
    refine ⟨k, hk, fun z => ?_, rfl⟩
    have hku : ConvexOn ℝ Set.univ (fun w => k w + u w) := hk.add hu
    have hku_le : ∀ w, k w + u w ≤ f w := fun w => by linarith [hkf w]
    linarith [le_convEnv hku hku_le z]
  · rintro ⟨k, hk, hkf, rfl⟩
    refine ⟨k, hk, fun z => ?_, rfl⟩
    linarith [hkf z, convEnv_le (hL.add hu) hLf' z]

private lemma convEnv_midpoint_of_lt {f L : ℝ → ℝ} (hf : Continuous f)
    (hL : ConvexOn ℝ Set.univ L) (hLf : ∀ z, L z ≤ f z) {x₀ : ℝ} (hlt : convEnv f x₀ < f x₀) :
    ∃ δ > 0, ∀ r, 0 < r → r ≤ δ →
      convEnv f x₀ = (convEnv f (x₀ - r) + convEnv f (x₀ + r)) / 2 := by
  set g := convEnv f
  have hg_conv : ConvexOn ℝ Set.univ g := convEnv_convexOn hL hLf
  have hg_cont : Continuous g := convex_continuous hg_conv
  set m := (g x₀ + f x₀) / 2
  have hgm : g x₀ < m := by dsimp only [m]; linarith
  have hmf : m < f x₀ := by dsimp only [m]; linarith
  have hev1 : ∀ᶠ z in 𝓝 x₀, g z < m := hg_cont.continuousAt.eventually (gt_mem_nhds hgm)
  have hev2 : ∀ᶠ z in 𝓝 x₀, m < f z := hf.continuousAt.eventually (lt_mem_nhds hmf)
  rw [Metric.eventually_nhds_iff] at hev1 hev2
  obtain ⟨δ₁, hδ₁, h1⟩ := hev1
  obtain ⟨δ₂, hδ₂, h2⟩ := hev2
  refine ⟨min δ₁ δ₂ / 2, by positivity, fun r hr hrδ => ?_⟩
  have hr1 : r < δ₁ := by linarith [min_le_left δ₁ δ₂]
  have hr2 : r < δ₂ := by linarith [min_le_right δ₁ δ₂]
  set a := x₀ - r
  set b := x₀ + r
  have hab : a < b := by linarith
  let c : ℝ → ℝ := fun z => g a + (g b - g a) / (b - a) * (z - a)
  let gtilde : ℝ → ℝ := fun z => max (g z) (c z)
  have hc_conv : ConvexOn ℝ Set.univ c := by
    refine ⟨convex_univ, fun z₁ _ z₂ _ s t _ _ hst => ?_⟩
    simp only [c, smul_eq_mul]
    have : s * z₁ + t * z₂ - a = s * (z₁ - a) + t * (z₂ - a) := by
      calc s * z₁ + t * z₂ - a = s * z₁ + t * z₂ - (s + t) * a := by rw [hst, one_mul]
        _ = s * (z₁ - a) + t * (z₂ - a) := by ring
    rw [this]
    have : g a = s * g a + t * g a := by rw [← add_mul, hst, one_mul]
    linarith
  have hgtilde_conv : ConvexOn ℝ Set.univ gtilde := hg_conv.sup hc_conv
  have hgtilde_le : ∀ z, gtilde z ≤ f z := fun z => by
    refine max_le (convEnv_le hL hLf z) ?_
    by_cases hz : z ∈ Icc a b
    · have hza : 0 ≤ z - a := sub_nonneg.mpr hz.1
      have hbz : 0 ≤ b - z := sub_nonneg.mpr hz.2
      have hba : 0 < b - a := sub_pos.mpr hab
      have hga : g a < m := h1 (by rw [Real.dist_eq]; simpa [a, abs_neg, abs_of_pos hr] using hr1)
      have hgb : g b < m := h1 (by rw [Real.dist_eq]; simpa [b, abs_of_pos hr] using hr1)
      have hfz : m < f z := h2 (by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2])
      have hc_le : c z ≤ max (g a) (g b) := by
        simp only [c]
        have hfrac : (z - a) / (b - a) ∈ Icc (0 : ℝ) 1 :=
          ⟨div_nonneg hza hba.le, (div_le_one hba).mpr (by linarith [hz.2])⟩
        have hlin : g a + (g b - g a) / (b - a) * (z - a) =
            (1 - (z - a) / (b - a)) * g a + ((z - a) / (b - a)) * g b := by
          field_simp [hba.ne']; ring
        rw [hlin]
        calc (1 - (z - a) / (b - a)) * g a + (z - a) / (b - a) * g b
            ≤ (1 - (z - a) / (b - a)) * max (g a) (g b) +
              (z - a) / (b - a) * max (g a) (g b) :=
              add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [hfrac.2]))
                (mul_le_mul_of_nonneg_left (le_max_right _ _) hfrac.1)
          _ = max (g a) (g b) := by ring
      linarith [max_lt hga hgb]
    · -- z < a or b < z: by convexity of g, c z ≤ g z ≤ f z
      have hcg : c z ≤ g z := by
        rcases lt_or_gt_of_ne (show z ≠ a from fun h => hz ⟨h.ge, h.le.trans hab.le⟩) with hza | haz
        · -- z < a < b
          have hbz : 0 < b - z := by linarith
          have ha_eq : a = ((b - a) / (b - z)) * z + ((a - z) / (b - z)) * b := by
            field_simp [hbz.ne']; ring
          have hconv : g (((b - a) / (b - z)) • z + ((a - z) / (b - z)) • b) ≤
              ((b - a) / (b - z)) • g z + ((a - z) / (b - z)) • g b :=
            hg_conv.2 (mem_univ z) (mem_univ b)
              (div_nonneg (by linarith) hbz.le) (div_nonneg (by linarith) hbz.le)
              (by field_simp [hbz.ne']; ring)
          simp only [smul_eq_mul] at hconv
          rw [← ha_eq] at hconv
          have hba : 0 < b - a := sub_pos.mpr hab
          have hmul1 : (b - z) * g a ≤ (b - a) * g z + (a - z) * g b := by
            have := mul_le_mul_of_nonneg_left hconv hbz.le
            have hrhs : (b - z) * ((b - a) / (b - z) * g z + (a - z) / (b - z) * g b) =
                (b - a) * g z + (a - z) * g b := by field_simp [hbz.ne']
            linarith
          simp only [c]
          have hmul2 : (b - a) * (g a + (g b - g a) / (b - a) * (z - a)) =
              (b - z) * g a - (a - z) * g b := by field_simp [hba.ne']; ring
          nlinarith
        · have hbz : b < z := by
            by_contra h; push Not at h; exact hz ⟨haz.le, h⟩
          have hza : 0 < z - a := by linarith
          have hb_eq : b = ((z - b) / (z - a)) * a + ((b - a) / (z - a)) * z := by
            field_simp [hza.ne']; ring
          have hconv : g (((z - b) / (z - a)) • a + ((b - a) / (z - a)) • z) ≤
              ((z - b) / (z - a)) • g a + ((b - a) / (z - a)) • g z :=
            hg_conv.2 (mem_univ a) (mem_univ z)
              (div_nonneg (by linarith) hza.le) (div_nonneg (by linarith) hza.le)
              (by field_simp [hza.ne']; ring)
          simp only [smul_eq_mul] at hconv
          rw [← hb_eq] at hconv
          have hba : 0 < b - a := sub_pos.mpr hab
          have hmul1 : (z - a) * g b ≤ (z - b) * g a + (b - a) * g z := by
            have := mul_le_mul_of_nonneg_left hconv hza.le
            have hrhs : (z - a) * ((z - b) / (z - a) * g a + (b - a) / (z - a) * g z) =
                (z - b) * g a + (b - a) * g z := by field_simp [hza.ne']
            linarith
          simp only [c]
          have hmul2 : (b - a) * (g a + (g b - g a) / (b - a) * (z - a)) =
              (z - a) * g b - (z - b) * g a := by field_simp [hba.ne']; ring
          nlinarith
      exact hcg.trans (convEnv_le hL hLf z)
  have hge : (g a + g b) / 2 ≤ g x₀ := by
    have hcx : c x₀ = (g a + g b) / 2 := by
      simp only [c, a, b]
      have h2r : x₀ + r - (x₀ - r) = 2 * r := by ring
      have hr' : x₀ - (x₀ - r) = r := by ring
      rw [h2r, hr']; field_simp [hr.ne']; ring
    rw [← hcx]
    exact (le_max_right (g x₀) (c x₀)).trans (le_convEnv hgtilde_conv hgtilde_le x₀)
  have hle : g x₀ ≤ (g a + g b) / 2 := by
    have hx_eq : x₀ = (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b := by simp only [a, b]; ring
    have hconv := hg_conv.2 (mem_univ a) (mem_univ b) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hconv
    rw [← hx_eq] at hconv
    linarith
  exact le_antisymm hle hge

private lemma convexOn_of_continuous_local_midpoint {h : ℝ → ℝ} (hh : Continuous h)
    (hloc : ∀ x₀ : ℝ, ∃ δ > 0, ∀ r, 0 < r → r ≤ δ → h x₀ ≤ (h (x₀ - r) + h (x₀ + r)) / 2) :
    ConvexOn ℝ Set.univ h := by
  have hchord : ∀ a b : ℝ, a < b → ∀ z ∈ Icc a b,
      h z ≤ h a + (h b - h a) / (b - a) * (z - a) := fun a b hab => by
    let ℓ : ℝ → ℝ := fun z => h a + (h b - h a) / (b - a) * (z - a)
    let d : ℝ → ℝ := fun z => h z - ℓ z
    have hd_cont : Continuous d :=
      hh.sub (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const)))
    have hda : d a = 0 := by simp [d, ℓ]
    have hdb : d b = 0 := by
      simp only [d, ℓ]; rw [div_mul_cancel₀ _ (sub_pos.mpr hab).ne']; ring
    intro z hz
    by_contra hgt
    push Not at hgt
    have hdz : 0 < d z := sub_pos.mpr hgt
    obtain ⟨xm, hxm_mem, hxm_max⟩ := isCompact_Icc.exists_isMaxOn ⟨z, hz⟩ hd_cont.continuousOn
    set M := d xm
    have hM_pos : 0 < M := lt_of_lt_of_le hdz (hxm_max hz)
    let K : Set ℝ := Icc a b ∩ {w | d w = M}
    have hK_ne : K.Nonempty := ⟨xm, hxm_mem, rfl⟩
    have hK_bdd : BddAbove K := ⟨b, fun w hw => hw.1.2⟩
    have hK_closed : IsClosed K := isClosed_Icc.inter (isClosed_eq hd_cont continuous_const)
    set x₀ := sSup K
    have hx₀_K : x₀ ∈ K := hK_closed.csSup_mem hK_ne hK_bdd
    have hx₀_eq : d x₀ = M := hx₀_K.2
    have hx₀_gt_a : a < x₀ := lt_of_le_of_ne hx₀_K.1.1 (fun h => by linarith [h ▸ hx₀_eq, hda])
    have hx₀_lt_b : x₀ < b := lt_of_le_of_ne hx₀_K.1.2 (fun h => by linarith [h ▸ hx₀_eq, hdb])
    obtain ⟨δ, hδ, hmid⟩ := hloc x₀
    set r := min δ (min (x₀ - a) (b - x₀)) / 2
    have hr_pos : 0 < r := by
      have : 0 < min (x₀ - a) (b - x₀) := lt_min (sub_pos.mpr hx₀_gt_a) (sub_pos.mpr hx₀_lt_b)
      positivity
    have hr_le_δ : r ≤ δ := by
      dsimp only [r]; linarith [min_le_left δ (min (x₀ - a) (b - x₀))]
    have hr_le_a : r ≤ x₀ - a := by
      dsimp only [r]; linarith [min_le_right δ (min (x₀ - a) (b - x₀)),
        min_le_left (x₀ - a) (b - x₀)]
    have hr_le_b : r ≤ b - x₀ := by
      dsimp only [r]; linarith [min_le_right δ (min (x₀ - a) (b - x₀)),
        min_le_right (x₀ - a) (b - x₀)]
    have hxm_l : d (x₀ - r) ≤ M := hxm_max ⟨by linarith, by linarith⟩
    have hxm_r_le : d (x₀ + r) ≤ M := hxm_max ⟨by linarith, by linarith⟩
    have hxm_r_ne : d (x₀ + r) ≠ M := fun heq => by
      have hmem : x₀ + r ∈ K := ⟨⟨by linarith, by linarith⟩, heq⟩
      linarith [le_csSup hK_bdd hmem]
    have hxm_r : d (x₀ + r) < M := lt_of_le_of_ne hxm_r_le hxm_r_ne
    have hℓ_mid : ℓ x₀ = (ℓ (x₀ - r) + ℓ (x₀ + r)) / 2 := by simp only [ℓ]; ring
    have hd_mid : d x₀ ≤ (d (x₀ - r) + d (x₀ + r)) / 2 := by
      have := hmid r hr_pos hr_le_δ
      simp only [d]; linarith
    linarith [hx₀_eq]
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
  simp only [smul_eq_mul]
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hmem : s * x + t * y ∈ Icc x y :=
      ⟨by have : s * x + t * y - x = t * (y - x) := by rw [show s = 1 - t by linarith]; ring
          nlinarith,
       by have : y - (s * x + t * y) = s * (y - x) := by rw [show t = 1 - s by linarith]; ring
          nlinarith⟩
    have := hchord x y hxy (s * x + t * y) hmem
    have hlin : h x + (h y - h x) / (y - x) * (s * x + t * y - x) = s * h x + t * h y := by
      have hs1 : s = 1 - t := by linarith
      rw [hs1]
      have hne : y - x ≠ 0 := (sub_pos.mpr hxy).ne'
      field_simp [hne]; ring
    linarith
  · rw [← add_mul, hst, one_mul, ← add_mul, hst, one_mul]
  · have hmem : s * x + t * y ∈ Icc y x :=
      ⟨by have : s * x + t * y - y = s * (x - y) := by rw [show t = 1 - s by linarith]; ring
          nlinarith,
       by have : x - (s * x + t * y) = t * (x - y) := by rw [show s = 1 - t by linarith]; ring
          nlinarith⟩
    have := hchord y x hyx (s * x + t * y) hmem
    have hlin : h y + (h x - h y) / (x - y) * (s * x + t * y - y) = s * h x + t * h y := by
      have ht1 : t = 1 - s := by linarith
      rw [ht1]
      have hne : x - y ≠ 0 := (sub_pos.mpr hyx).ne'
      field_simp [hne]; ring
    linarith

private lemma sub_convEnv_convexOn {u v L : ℝ → ℝ}
    (hu : ConvexOn ℝ Set.univ u) (hv : ConvexOn ℝ Set.univ v)
    (hL : ConvexOn ℝ Set.univ L) (hLvu : ∀ z, L z ≤ v z - u z) :
    ConvexOn ℝ Set.univ (fun x => v x - convEnv (fun z => v z - u z) x) := by
  set f := fun z => v z - u z
  set g := convEnv f
  have hf_cont : Continuous f := (convex_continuous hv).sub (convex_continuous hu)
  have hg_conv : ConvexOn ℝ Set.univ g := convEnv_convexOn hL hLvu
  have hh_cont : Continuous (fun x => v x - g x) :=
    (convex_continuous hv).sub (convex_continuous hg_conv)
  refine convexOn_of_continuous_local_midpoint hh_cont fun x₀ => ?_
  rcases lt_or_eq_of_le (convEnv_le hL hLvu x₀) with hlt | heq
  · obtain ⟨δ, hδ, hmid_g⟩ := convEnv_midpoint_of_lt hf_cont hL hLvu hlt
    refine ⟨δ, hδ, fun r hr hrδ => ?_⟩
    have hmid_v : v x₀ ≤ (v (x₀ - r) + v (x₀ + r)) / 2 := by
      have hx_eq : x₀ = (1 / 2 : ℝ) * (x₀ - r) + (1 / 2 : ℝ) * (x₀ + r) := by ring
      have hc := hv.2 (mem_univ (x₀ - r)) (mem_univ (x₀ + r))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hc; rw [← hx_eq] at hc; linarith
    linarith [hmid_g r hr hrδ]
  · refine ⟨1, zero_lt_one, fun r _ _ => ?_⟩
    have hux : v x₀ - g x₀ = u x₀ := by
      have : g x₀ = v x₀ - u x₀ := heq
      linarith
    have hmid_u : u x₀ ≤ (u (x₀ - r) + u (x₀ + r)) / 2 := by
      have hx_eq : x₀ = (1 / 2 : ℝ) * (x₀ - r) + (1 / 2 : ℝ) * (x₀ + r) := by ring
      have hc := hu.2 (mem_univ (x₀ - r)) (mem_univ (x₀ + r))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at hc; rw [← hx_eq] at hc; linarith
    have hu_le : ∀ z, u z ≤ v z - g z := fun z => by
      have : g z ≤ v z - u z := convEnv_le hL hLvu z
      linarith
    linarith [hu_le (x₀ - r), hu_le (x₀ + r)]

/-! ### Section E: Shadow potential identity -/

private lemma shadow_potential_eq {μ ν η : Measure ℝ}
    (hE : MartOT.Var.ExtConvexLE μ ν) (hS : MartOT.Var.IsShadow ν μ η) :
    ∀ x, MartOT.Var.potential ν x - MartOT.Var.potential η x =
      convEnv (fun z => MartOT.Var.potential ν z - MartOT.Var.potential μ z) x := by
  have hμ := hE.1
  have hν := hE.2.1
  have hη := inM_of_le hS.1 hν
  set f := fun z => MartOT.Var.potential ν z - MartOT.Var.potential μ z
  set g := convEnv f
  let L : ℝ → ℝ := fun z => |(mass ν - mass μ) * z - (mean ν - mean μ)|
  have hL_conv : ConvexOn ℝ Set.univ L := by
    refine ⟨convex_univ, fun z₁ _ z₂ _ a b ha hb hab => ?_⟩
    simp only [L, smul_eq_mul]
    have heq : (mass ν - mass μ) * (a * z₁ + b * z₂) - (mean ν - mean μ) =
        a * ((mass ν - mass μ) * z₁ - (mean ν - mean μ)) +
        b * ((mass ν - mass μ) * z₂ - (mean ν - mean μ)) := by
      calc (mass ν - mass μ) * (a * z₁ + b * z₂) - (mean ν - mean μ)
          = (mass ν - mass μ) * (a * z₁ + b * z₂) - (a + b) * (mean ν - mean μ) := by
            rw [hab, one_mul]
        _ = _ := by ring
    rw [heq]
    calc |a * ((mass ν - mass μ) * z₁ - (mean ν - mean μ)) +
          b * ((mass ν - mass μ) * z₂ - (mean ν - mean μ))|
        ≤ |a * ((mass ν - mass μ) * z₁ - (mean ν - mean μ))| +
          |b * ((mass ν - mass μ) * z₂ - (mean ν - mean μ))| := abs_add_le _ _
      _ = a * |(mass ν - mass μ) * z₁ - (mean ν - mean μ)| +
          b * |(mass ν - mass μ) * z₂ - (mean ν - mean μ)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hLf : ∀ z, L z ≤ f z := extConvexLE_potential_lower hE
  -- Direction 1: u_ν - u_η ≤ g
  have hle_g : ∀ x, MartOT.Var.potential ν x - MartOT.Var.potential η x ≤ g x := by
    have hdiff_conv : ConvexOn ℝ Set.univ
        (fun z => MartOT.Var.potential ν z - MartOT.Var.potential η z) := by
      have heq : (fun z => MartOT.Var.potential ν z - MartOT.Var.potential η z) =
          MartOT.Var.potential (ν - η) := by
        ext z; exact (potential_sub_eq hS.1 hν z).symm
      rw [heq]
      exact potential_convexOn (inM_of_le Measure.sub_le hν)
    have hdiff_le : ∀ z, MartOT.Var.potential ν z - MartOT.Var.potential η z ≤ f z := fun z => by
      simp only [f]; linarith [convexLE_potential_le hS.2.1 z]
    exact fun x => le_convEnv hdiff_conv hdiff_le x
  -- Direction 2: g ≤ u_ν - u_η
  have hg_conv : ConvexOn ℝ Set.univ g := convEnv_convexOn hL_conv hLf
  have hh_conv : ConvexOn ℝ Set.univ (fun z => MartOT.Var.potential ν z - g z) :=
    sub_convEnv_convexOn (potential_convexOn hμ) (potential_convexOn hν) hL_conv hLf
  have hf_top : Tendsto
      (fun x => f x - ((mass ν - mass μ) * x - (mean ν - mean μ))) atTop (𝓝 0) := by
    have := (potential_tendsto_top hν).sub (potential_tendsto_top hμ)
    rw [sub_self] at this
    exact this.congr fun x => by simp only [f]; ring
  have hf_bot : Tendsto
      (fun x => f x - (-(mass ν - mass μ) * x + (mean ν - mean μ))) atBot (𝓝 0) := by
    have := (potential_tendsto_bot hν).sub (potential_tendsto_bot hμ)
    rw [sub_self] at this
    exact this.congr fun x => by simp only [f]; ring
  have hg_top : Tendsto
      (fun x => g x - ((mass ν - mass μ) * x - (mean ν - mean μ))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf_top
      (fun x => by
        have h1 : (mass ν - mass μ) * x - (mean ν - mean μ) ≤ L x := le_abs_self _
        linarith [le_convEnv hL_conv hLf x])
      (fun x => by linarith [convEnv_le hL_conv hLf x])
  have hg_bot : Tendsto
      (fun x => g x - (-(mass ν - mass μ) * x + (mean ν - mean μ))) atBot (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf_bot
      (fun x => by
        have h1 : -((mass ν - mass μ) * x - (mean ν - mean μ)) ≤ L x := neg_le_abs _
        linarith [le_convEnv hL_conv hLf x])
      (fun x => by linarith [convEnv_le hL_conv hLf x])
  have hh_top : Tendsto
      (fun x => (MartOT.Var.potential ν x - g x) - (mass μ * x - mean μ)) atTop (𝓝 0) := by
    have := (potential_tendsto_top hν).sub hg_top
    rw [sub_self] at this
    exact this.congr fun x => by ring
  have hh_bot : Tendsto
      (fun x => (MartOT.Var.potential ν x - g x) - (-mass μ * x + mean μ)) atBot (𝓝 0) := by
    have := (potential_tendsto_bot hν).sub hg_bot
    rw [sub_self] at this
    exact this.congr fun x => by ring
  obtain ⟨θg, hθg_inM, _, _, hθg_pot⟩ := convex_stieltjes_exists hg_conv hg_top hg_bot
  obtain ⟨θh, hθh_inM, hθh_mass, hθh_mean, hθh_pot⟩ := convex_stieltjes_exists hh_conv hh_top hh_bot
  have hsum : θg + θh = ν := measure_add_of_potential_add hθg_inM hθh_inM hν fun x => by
    rw [hθg_pot x, hθh_pot x]; ring
  have hθh_le : θh ≤ ν := by rw [← hsum]; exact Measure.le_add_left le_rfl
  have hμ_le_θh : MartOT.Var.ConvexLE μ θh :=
    convexLE_of_potential_le hμ hθh_inM hθh_mass.symm hθh_mean.symm fun x => by
      rw [hθh_pot x]; linarith [convEnv_le hL_conv hLf x]
  have hη_le_θh : MartOT.Var.ConvexLE η θh := hS.2.2 θh hθh_le hμ_le_θh
  intro x
  have hge_g : g x ≤ MartOT.Var.potential ν x - MartOT.Var.potential η x := by
    have := convexLE_potential_le hη_le_θh x
    rw [hθh_pot x] at this; linarith
  exact le_antisymm (hle_g x) hge_g

end Lemma416Helpers

open MeasureTheory NNReal

theorem solution (α : ℝ≥0) (x : ℝ) (γ ν : Measure ℝ) (hγ : MartOT.Var.InM γ) (hν : MartOT.Var.InM ν)
    (h : MartOT.Var.ExtConvexLE (γ + (α : ENNReal) • Measure.dirac x) ν) :
    ∀ η1 : Measure ℝ, MartOT.Var.IsShadow ν γ η1 →
      ∀ η : Measure ℝ, MartOT.Var.IsShadow ν (γ + (α : ENNReal) • Measure.dirac x) η →
        η1 ≤ η ∧ MartOT.Var.ExtConvexLE ((α : ENNReal) • Measure.dirac x) (η - η1) ∧
        ∀ η2 : Measure ℝ, MartOT.Var.IsShadow (ν - η1) ((α : ENNReal) • Measure.dirac x) η2 →
          η = η1 + η2 := by
  open Lemma416Helpers Filter Topology in
  set δ : Measure ℝ := (α : ENNReal) • Measure.dirac x
  have hδ : MartOT.Var.InM δ := inM_smul_dirac α x
  have hγδ : MartOT.Var.InM (γ + δ) := inM_add hγ hδ
  have hEγ : MartOT.Var.ExtConvexLE γ ν := by
    refine ⟨hγ, hν, fun ϕ hϕ hϕ0 => ?_⟩
    exact (lintegral_mono' (Measure.le_add_right le_rfl) le_rfl).trans (h.2.2 ϕ hϕ hϕ0)
  intro η1 hS1 η hS
  have hη1 : MartOT.Var.InM η1 := inM_of_le hS1.1 hν
  have hη : MartOT.Var.InM η := inM_of_le hS.1 hν
  have hνsub1 : MartOT.Var.InM (ν - η1) := inM_of_le Measure.sub_le hν
  have hg1_eq : ∀ z, MartOT.Var.potential ν z - MartOT.Var.potential η1 z =
      convEnv (fun w => MartOT.Var.potential ν w - MartOT.Var.potential γ w) z :=
    shadow_potential_eq hEγ hS1
  have hg_eq : ∀ z, MartOT.Var.potential ν z - MartOT.Var.potential η z =
      convEnv (fun w => (MartOT.Var.potential ν w - MartOT.Var.potential γ w) -
        MartOT.Var.potential δ w) z := fun z => by
    have h1 := shadow_potential_eq h hS z
    have hfun : (fun w => MartOT.Var.potential ν w - MartOT.Var.potential (γ + δ) w) =
        fun w => (MartOT.Var.potential ν w - MartOT.Var.potential γ w) -
          MartOT.Var.potential δ w := by
      ext w; rw [potential_add hγ hδ w]; ring
    rwa [hfun] at h1
  -- Convex minorant for (u_ν - u_γ) - u_δ: use u_{ν - η} = u_ν - u_η!
  have hminor_conv : ConvexOn ℝ Set.univ
      (fun z => MartOT.Var.potential ν z - MartOT.Var.potential η z) := by
    have heq : (fun z => MartOT.Var.potential ν z - MartOT.Var.potential η z) =
        MartOT.Var.potential (ν - η) := by
      ext z; exact (potential_sub_eq hS.1 hν z).symm
    rw [heq]; exact potential_convexOn (inM_of_le Measure.sub_le hν)
  have hminor_le : ∀ z, MartOT.Var.potential ν z - MartOT.Var.potential η z ≤
      (MartOT.Var.potential ν z - MartOT.Var.potential γ z) - MartOT.Var.potential δ z := fun z => by
    have h1 := convexLE_potential_le hS.2.1 z
    rw [potential_add hγ hδ z] at h1; linarith
  -- Key identity: convEnv ((u_ν - u_γ) - u_δ) = convEnv (u_{ν - η1} - u_δ)
  have hg_eq' : ∀ z, MartOT.Var.potential ν z - MartOT.Var.potential η z =
      convEnv (fun w => MartOT.Var.potential (ν - η1) w - MartOT.Var.potential δ w) z := fun z => by
    rw [hg_eq z, convEnv_sub_convex (potential_convexOn hδ) hminor_conv hminor_le z]
    congr 1; ext w
    rw [← hg1_eq w, potential_sub_eq hS1.1 hν w]
  have hminor_le' : ∀ z, MartOT.Var.potential ν z - MartOT.Var.potential η z ≤
      MartOT.Var.potential (ν - η1) z - MartOT.Var.potential δ z := fun z => by
    have hsum_conv : ConvexOn ℝ Set.univ
        (fun w => (MartOT.Var.potential ν w - MartOT.Var.potential η w) +
          MartOT.Var.potential δ w) := hminor_conv.add (potential_convexOn hδ)
    have hsum_le : ∀ w, (MartOT.Var.potential ν w - MartOT.Var.potential η w) +
        MartOT.Var.potential δ w ≤ MartOT.Var.potential ν w - MartOT.Var.potential γ w := fun w => by
      linarith [hminor_le w]
    have hle := le_convEnv hsum_conv hsum_le z
    rw [← hg1_eq z, ← potential_sub_eq hS1.1 hν z] at hle
    linarith
  -- Therefore u_η - u_{η1} = u_{ν - η1} - (u_ν - u_η) is convex!
  have hh2_conv : ConvexOn ℝ Set.univ
      (fun z => MartOT.Var.potential η z - MartOT.Var.potential η1 z) := by
    have hsub := sub_convEnv_convexOn (potential_convexOn hδ) (potential_convexOn hνsub1)
      hminor_conv hminor_le'
    have heq : (fun z => MartOT.Var.potential (ν - η1) z -
        convEnv (fun w => MartOT.Var.potential (ν - η1) w - MartOT.Var.potential δ w) z) =
        fun z => MartOT.Var.potential η z - MartOT.Var.potential η1 z := by
      ext z; rw [← hg_eq' z, potential_sub_eq hS1.1 hν z]; ring
    rwa [heq] at hsub
  -- Asymptotics of u_η - u_{η1} match δ
  have hmass_η1 : mass η1 = mass γ := (convexLE_mass_eq hS1.2.1).symm
  have hmean_η1 : mean η1 = mean γ := (convexLE_mean_eq hS1.2.1).symm
  have hmass_η : mass η = mass γ + mass δ := by
    have := hγ.1; have := hδ.1
    rw [← convexLE_mass_eq hS.2.1, mass, Measure.add_apply,
      ENNReal.toReal_add (measure_ne_top γ _) (measure_ne_top δ _)]
  have hmean_η : mean η = mean γ + mean δ := by
    rw [← convexLE_mean_eq hS.2.1, mean, integral_add_measure hγ.2 hδ.2]; rfl
  have hh2_top : Tendsto
      (fun z => (MartOT.Var.potential η z - MartOT.Var.potential η1 z) -
        (mass δ * z - mean δ)) atTop (𝓝 0) := by
    have := (potential_tendsto_top hη).sub (potential_tendsto_top hη1)
    rw [sub_self] at this
    exact this.congr fun z => by rw [hmass_η, hmass_η1, hmean_η, hmean_η1]; ring
  have hh2_bot : Tendsto
      (fun z => (MartOT.Var.potential η z - MartOT.Var.potential η1 z) -
        (-mass δ * z + mean δ)) atBot (𝓝 0) := by
    have := (potential_tendsto_bot hη).sub (potential_tendsto_bot hη1)
    rw [sub_self] at this
    exact this.congr fun z => by rw [hmass_η, hmass_η1, hmean_η, hmean_η1]; ring
  obtain ⟨θ, hθ_inM, hθ_mass, hθ_mean, hθ_pot⟩ := convex_stieltjes_exists hh2_conv hh2_top hh2_bot
  have hη_eq : η1 + θ = η := measure_add_of_potential_add hη1 hθ_inM hη fun z => by
    rw [hθ_pot z]; ring
  -- Part 1: η1 ≤ η
  have hη1_le_η : η1 ≤ η := by rw [← hη_eq]; exact Measure.le_add_right le_rfl
  -- Also η - η1 = θ
  have hsub_eq_θ : η - η1 = θ := by
    have := hη1.1
    rw [← hη_eq, add_comm, Measure.add_sub_cancel]
  -- Part 2: δ ⪯_C θ (hence δ ⪯_E η - η1)
  have hδ_le_θ : MartOT.Var.ConvexLE δ θ :=
    convexLE_of_potential_le hδ hθ_inM hθ_mass.symm hθ_mean.symm fun z => by
      rw [hθ_pot z]
      have h1 := hminor_le' z
      rw [potential_sub_eq hS1.1 hν z] at h1
      linarith
  have hδ_E : MartOT.Var.ExtConvexLE δ (η - η1) := by
    rw [hsub_eq_θ]; exact convexLE_imp_extConvexLE hδ_le_θ
  refine ⟨hη1_le_η, hδ_E, fun η2 hS2 => ?_⟩
  -- Part 3: η = η1 + η2
  have := hη1.1
  have hη2_inM : MartOT.Var.InM η2 := inM_of_le hS2.1 hνsub1
  have hη12_le_ν : η1 + η2 ≤ ν := by
    calc η1 + η2 ≤ η1 + (ν - η1) := add_le_add le_rfl hS2.1
      _ = ν := by rw [add_comm, Measure.sub_add_cancel_of_le hS1.1]
  have hγδ_le_η12 : MartOT.Var.ConvexLE (γ + δ) (η1 + η2) := by
    have := hγ.1; have := hδ.1; have := hη2_inM.1
    refine convexLE_of_potential_le hγδ (inM_add hη1 hη2_inM) ?_ ?_ fun z => ?_
    · rw [mass, mass, Measure.add_apply, Measure.add_apply,
        ENNReal.toReal_add (measure_ne_top γ _) (measure_ne_top δ _),
        ENNReal.toReal_add (measure_ne_top η1 _) (measure_ne_top η2 _)]
      exact congrArg₂ (· + ·) (convexLE_mass_eq hS1.2.1) (convexLE_mass_eq hS2.2.1)
    · rw [mean, mean, integral_add_measure hγ.2 hδ.2, integral_add_measure hη1.2 hη2_inM.2]
      exact congrArg₂ (· + ·) (convexLE_mean_eq hS1.2.1) (convexLE_mean_eq hS2.2.1)
    · rw [potential_add hγ hδ z, potential_add hη1 hη2_inM z]
      exact add_le_add (convexLE_potential_le hS1.2.1 z) (convexLE_potential_le hS2.2.1 z)
  have hη_le_η12 : MartOT.Var.ConvexLE η (η1 + η2) := hS.2.2 (η1 + η2) hη12_le_ν hγδ_le_η12
  have hθ_le_νsub : θ ≤ ν - η1 := by
    rw [← hsub_eq_θ]
    exact (Measure.sub_le_iff_le_add_of_le hη1_le_η).mpr (by
      rw [Measure.sub_add_cancel_of_le hS1.1]; exact hS.1)
  have hη2_le_θ : MartOT.Var.ConvexLE η2 θ := hS2.2.2 θ hθ_le_νsub hδ_le_θ
  refine measure_eq_of_potential_eq hη (inM_add hη1 hη2_inM) fun z => le_antisymm ?_ ?_
  · exact convexLE_potential_le hη_le_η12 z
  · rw [potential_add hη1 hη2_inM z, ← hη_eq, potential_add hη1 hθ_inM z]
    exact add_le_add le_rfl (convexLE_potential_le hη2_le_θ z)
