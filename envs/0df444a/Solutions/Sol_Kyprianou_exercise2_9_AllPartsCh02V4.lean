-- Prove2me | solution 1 for Kyprianou.exercise2_9_AllPartsCh02V4
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:08:08.931627+00:00
-- url     : https://prove2.me/submissions/aa2b5df0-3155-4d0a-9f49-e1c915b0a52d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_Kyprianou_poissonRandomMeasureExists
import Theorems.Thm_Kyprianou_finiteRegionPoissonIntegralCh02V3

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Exercise29Helpers

/-! ### Section 1: Positivity and Complex Factorization for αpos, αneg -/

private lemma disc_gt_abs (α c σ : ℝ) (hα : 0 < α) (hσ : 0 < σ) :
    |c / (2 * α)| < Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α)) := by
  have h1 : |c / (2 * α)| ^ 2 = c ^ 2 / (4 * α ^ 2) := by
    rw [sq_abs, div_pow]; ring
  have h2 : 0 < σ ^ 2 / (2 * α) := by positivity
  have hlt : |c / (2 * α)| ^ 2 < c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α) := by linarith
  have hnonneg : 0 ≤ |c / (2 * α)| := abs_nonneg _
  calc |c / (2 * α)| = Real.sqrt (|c / (2 * α)| ^ 2) := (Real.sqrt_sq hnonneg).symm
    _ < Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α)) :=
      Real.sqrt_lt_sqrt (sq_nonneg _) hlt

private lemma alpha_pos_pos (α c σ : ℝ) (hα : 0 < α) (hσ : 0 < σ) :
    0 < (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α)) + c / (2 * α))⁻¹ := by
  have h := disc_gt_abs α c σ hα hσ
  have hneg : -(c / (2 * α)) ≤ |c / (2 * α)| := neg_le_abs _
  exact inv_pos.mpr (by linarith)

private lemma alpha_neg_pos (α c σ : ℝ) (hα : 0 < α) (hσ : 0 < σ) :
    0 < (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α)) - c / (2 * α))⁻¹ := by
  have h := disc_gt_abs α c σ hα hσ
  have hle : c / (2 * α) ≤ |c / (2 * α)| := le_abs_self _
  exact inv_pos.mpr (by linarith)

private lemma vg_complex_factorization (α c σ ξ : ℝ) (hα : 0 < α) (hσ : 0 < σ) :
    let αpos : ℝ := (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α)) + c / (2 * α))⁻¹
    let αneg : ℝ := (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α)) - c / (2 * α))⁻¹
    (1 - Complex.I * (((ξ / αpos : ℝ) : ℂ))) *
      (1 + Complex.I * (((ξ / αneg : ℝ) : ℂ))) =
    1 - Complex.I * (((ξ * c / α : ℝ) : ℂ)) +
      (((σ ^ 2 * ξ ^ 2 / (2 * α) : ℝ) : ℂ)) := by
  intro αpos αneg
  have hDnn : 0 ≤ c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α) := by positivity
  have hDsq : Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α)) ^ 2 =
      c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α) := Real.sq_sqrt hDnn
  have hsub : αpos⁻¹ - αneg⁻¹ = c / α := by
    dsimp [αpos, αneg]
    rw [inv_inv, inv_inv]
    ring
  have hmul : αpos⁻¹ * αneg⁻¹ = σ ^ 2 / (2 * α) := by
    dsimp [αpos, αneg]
    rw [inv_inv, inv_inv]
    have hdiff : (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α)) + c / (2 * α)) *
        (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α)) - c / (2 * α)) =
        Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α)) ^ 2 - (c / (2 * α)) ^ 2 := by ring
    rw [hdiff, hDsq]; ring
  have h1 : ξ / αpos = ξ * αpos⁻¹ := div_eq_mul_inv ξ αpos
  have h2 : ξ / αneg = ξ * αneg⁻¹ := div_eq_mul_inv ξ αneg
  rw [h1, h2]
  apply Complex.ext
  · simp only [mul_re, sub_re, add_re, one_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im,
      mul_zero, sub_zero, one_mul, mul_im, add_zero, sub_im, add_im, one_im, zero_add,
      zero_sub, neg_mul, sub_neg_eq_add]
    have : ξ * αpos⁻¹ * (ξ * αneg⁻¹) = ξ ^ 2 * (αpos⁻¹ * αneg⁻¹) := by ring
    rw [this, hmul]
    ring
  · simp only [mul_im, mul_re, sub_re, add_re, one_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im,
      mul_zero, sub_zero, one_mul, mul_one, sub_im, add_im, one_im, zero_add, zero_sub, add_zero]
    have : ξ * αneg⁻¹ + -(ξ * αpos⁻¹) = -(ξ * (αpos⁻¹ - αneg⁻¹)) := by ring
    rw [this, hsub]
    ring

private lemma arg_abs_lt_pi_div_two_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    |z.arg| < Real.pi / 2 := by
  have hne : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hcos : 0 < Real.cos z.arg := by
    rw [Complex.cos_arg hne]
    exact div_pos hz (norm_pos_iff.mpr hne)
  have hmem := Complex.arg_mem_Ioc z
  rw [abs_lt]
  constructor
  · by_contra hle
    push Not at hle
    have hcos' : Real.cos (-z.arg) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [hmem.1])
    rw [Real.cos_neg] at hcos'
    linarith
  · by_contra hle
    push Not at hle
    have hcos' : Real.cos z.arg ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hle (by linarith [hmem.2])
    linarith

private lemma vg_complex_log_add (α c σ ξ : ℝ) (hα : 0 < α) (hσ : 0 < σ) :
    let αpos : ℝ := (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α)) + c / (2 * α))⁻¹
    let αneg : ℝ := (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α)) - c / (2 * α))⁻¹
    Complex.log (1 - Complex.I * (((ξ / αpos : ℝ) : ℂ))) +
      Complex.log (1 + Complex.I * (((ξ / αneg : ℝ) : ℂ))) =
    Complex.log (1 - Complex.I * (((ξ * c / α : ℝ) : ℂ)) +
      (((σ ^ 2 * ξ ^ 2 / (2 * α) : ℝ) : ℂ))) := by
  intro αpos αneg
  let w₁ : ℂ := 1 - Complex.I * (((ξ / αpos : ℝ) : ℂ))
  let w₂ : ℂ := 1 + Complex.I * (((ξ / αneg : ℝ) : ℂ))
  have hw₁_re : 0 < w₁.re := by simp [w₁]
  have hw₂_re : 0 < w₂.re := by simp [w₂]
  have hw₁_ne : w₁ ≠ 0 := fun h => by rw [h] at hw₁_re; simp at hw₁_re
  have hw₂_ne : w₂ ≠ 0 := fun h => by rw [h] at hw₂_re; simp at hw₂_re
  have ha₁ : |w₁.arg| < Real.pi / 2 := arg_abs_lt_pi_div_two_of_re_pos hw₁_re
  have ha₂ : |w₂.arg| < Real.pi / 2 := arg_abs_lt_pi_div_two_of_re_pos hw₂_re
  have hsum : w₁.arg + w₂.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [abs_lt] at ha₁ ha₂
    exact ⟨by linarith, by linarith⟩
  rw [← Complex.log_mul hw₁_ne hw₂_ne hsum]
  exact congrArg Complex.log (vg_complex_factorization α c σ ξ hα hσ)

/-! ### Section 2: Joint Characteristic Function -> Independence & IdentDistrib -/

private lemma integrable_pi_fin_prod {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ k, IsProbabilityMeasure (μ k)] (g : Fin n → ℝ → ℂ)
    (hg : ∀ k, Integrable (g k) (μ k)) :
    Integrable (fun x : Fin n → ℝ => ∏ k : Fin n, g k (x k)) (Measure.pi μ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmp := measurePreserving_piFinSuccAbove μ 0
    have hrew : (fun x : Fin (n + 1) → ℝ => ∏ k : Fin (n + 1), g k (x k)) =
        (fun p : ℝ × (Fin n → ℝ) => g 0 p.1 * ∏ k : Fin n, g k.succ (p.2 k)) ∘
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) := by
      funext x
      simp [Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove, Fin.tail]
    rw [hrew]
    have hprod : Integrable (fun p : ℝ × (Fin n → ℝ) => g 0 p.1 * ∏ k : Fin n, g k.succ (p.2 k))
        ((μ 0).prod (Measure.pi (fun j : Fin n => μ (Fin.succAbove 0 j)))) := by
      have h2 := ih (fun j => μ (Fin.succAbove 0 j)) (fun j => g j.succ)
        (fun j => by simpa [Fin.succAbove_zero] using hg j.succ)
      exact Integrable.mul_prod (hg 0) h2
    exact (hmp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).measurableEmbedding).mpr hprod

private lemma integral_pi_fin_prod {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ k, IsProbabilityMeasure (μ k)] (g : Fin n → ℝ → ℂ)
    (hg : ∀ k, Integrable (g k) (μ k)) :
    ∫ x : Fin n → ℝ, (∏ k : Fin n, g k (x k)) ∂(Measure.pi μ) =
      ∏ k : Fin n, ∫ y : ℝ, g k y ∂(μ k) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hmp := measurePreserving_piFinSuccAbove μ 0
    have hrew : ∀ x : Fin (n + 1) → ℝ, (∏ k : Fin (n + 1), g k (x k)) =
        g 0 ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) x).1 *
          ∏ k : Fin n, g k.succ (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) x).2 k) := by
      intro x
      simp [Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove, Fin.tail]
    have hcomp := hmp.integral_comp
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).measurableEmbedding
      (fun p : ℝ × (Fin n → ℝ) => g 0 p.1 * ∏ k : Fin n, g k.succ (p.2 k))
    simp_rw [hrew]
    rw [hcomp]
    have hprod_int : Integrable (fun p : ℝ × (Fin n → ℝ) =>
        g 0 p.1 * ∏ k : Fin n, g k.succ (p.2 k))
        ((μ 0).prod (Measure.pi (fun j : Fin n => μ (Fin.succAbove 0 j)))) :=
      Integrable.mul_prod (hg 0) (integrable_pi_fin_prod (fun j => μ (Fin.succAbove 0 j))
        (fun j => g j.succ) (fun j => by simpa [Fin.succAbove_zero] using hg j.succ))
    rw [integral_prod _ hprod_int]
    simp_rw [integral_const_mul]
    rw [integral_mul_const, ih (fun j => μ (Fin.succAbove 0 j)) (fun j => g j.succ)
      (fun j => by simpa [Fin.succAbove_zero] using hg j.succ), Fin.prod_univ_succ]
    simp

private lemma iIndepFun_of_joint_charFun {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (Y : Fin n → Ω → ℝ) (hY : ∀ k, AEMeasurable (Y k) P)
    (hchar : ∀ ξ : Fin n → ℝ,
      ∫ ω, Complex.exp (∑ k : Fin n, Complex.I * (ξ k : ℂ) * ((Y k ω : ℝ) : ℂ)) ∂P =
        ∏ k : Fin n, charFun (P.map (Y k)) (ξ k)) :
    iIndepFun Y P := by
  rw [iIndepFun_iff_map_fun_eq_pi_map hY]
  let e : (Fin n → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin n) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ))
  let μ₁ : Measure (Fin n → ℝ) := P.map (fun ω k => Y k ω)
  let μ₂ : Measure (Fin n → ℝ) := Measure.pi (fun k => P.map (Y k))
  have hYfun : AEMeasurable (fun ω k => Y k ω) P := aemeasurable_pi_lambda _ hY
  have : IsProbabilityMeasure μ₁ := Measure.isProbabilityMeasure_map hYfun
  have : ∀ k, IsProbabilityMeasure (P.map (Y k)) := fun k => Measure.isProbabilityMeasure_map (hY k)
  have : IsProbabilityMeasure μ₂ := inferInstance
  have hmap_eq : μ₁.map e = μ₂.map e := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_apply, charFun_apply]
    have hinner : ∀ x : Fin n → ℝ,
        (inner ℝ (e x) t : ℝ) = ∑ k : Fin n, t.ofLp k * x k := by
      intro x
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct, e]
    have hlhs : ∫ y, Complex.exp (((inner ℝ y t : ℝ) : ℂ) * Complex.I) ∂(μ₁.map e) =
        ∫ ω, Complex.exp (∑ k : Fin n, Complex.I * (t.ofLp k : ℂ) * ((Y k ω : ℝ) : ℂ)) ∂P := by
      rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hYfun]
      rw [integral_map (e.measurable.comp_aemeasurable hYfun)]
      · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        dsimp only [Function.comp_apply]
        congr 1
        rw [hinner]
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      · exact (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)).mul
            continuous_const)).aestronglyMeasurable
    have hrhs : ∫ y, Complex.exp (((inner ℝ y t : ℝ) : ℂ) * Complex.I) ∂(μ₂.map e) =
        ∏ k : Fin n, charFun (P.map (Y k)) (t.ofLp k) := by
      rw [integral_map e.measurable.aemeasurable]
      · have hrew : (fun x : Fin n → ℝ => Complex.exp (((inner ℝ (e x) t : ℝ) : ℂ) * Complex.I)) =
            (fun x : Fin n → ℝ => ∏ k : Fin n,
              Complex.exp (Complex.I * (t.ofLp k : ℂ) * ((x k : ℝ) : ℂ))) := by
          funext x
          rw [← Complex.exp_sum, hinner]
          congr 1
          push_cast
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
        rw [hrew, integral_pi_fin_prod (fun k => P.map (Y k))
          (fun k y => Complex.exp (Complex.I * (t.ofLp k : ℂ) * ((y : ℝ) : ℂ)))]
        · refine Finset.prod_congr rfl fun k _ => ?_
          rw [charFun_apply_real]
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          ring
        · intro k
          refine Integrable.of_bound
            ((Complex.continuous_exp.comp
              (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable) 1 ?_
          refine Eventually.of_forall fun y => ?_
          have : (Complex.I * (t.ofLp k : ℂ) * (y : ℂ)).re = 0 := by simp
          rw [Complex.norm_exp, this, Real.exp_zero]
      · exact (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)).mul
            continuous_const)).aestronglyMeasurable
    rw [hlhs, hrhs, hchar t.ofLp]
  calc μ₁ = (μ₁.map e).map e.symm := by
        rw [Measure.map_map e.symm.measurable e.measurable]; simp
    _ = (μ₂.map e).map e.symm := by rw [hmap_eq]
    _ = μ₂ := by rw [Measure.map_map e.symm.measurable e.measurable]; simp

private lemma identDistrib_of_charFun {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {f g : Ω → ℝ}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (hchar : ∀ ξ : ℝ, charFun (P.map f) ξ = charFun (P.map g) ξ) :
    IdentDistrib f g P P := by
  have : IsProbabilityMeasure (P.map f) := Measure.isProbabilityMeasure_map hf
  have : IsProbabilityMeasure (P.map g) := Measure.isProbabilityMeasure_map hg
  exact ⟨hf, hg, Measure.ext_of_charFun (funext hchar)⟩

/-! ### Section 3: Analytic Continuation of Gamma Laplace Transform -/

private lemma exp_neg_mul_norm_le_one {z : ℂ} (hz : 0 ≤ z.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.exp (-z * (x : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hre : (-z * (x : ℂ)).re = -z.re * x := by simp
  rw [hre]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

private lemma mul_exp_neg_le_inv {r x : ℝ} (hr : 0 < r) (_hx : 0 ≤ x) :
    x * Real.exp (-r * x) ≤ r⁻¹ := by
  have h1 : r * x ≤ Real.exp (r * x) := by linarith [Real.add_one_le_exp (r * x)]
  have h2 : Real.exp (r * x) * Real.exp (-r * x) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-r * x) := Real.exp_pos _
  have h3 : r * (x * Real.exp (-r * x)) ≤ 1 := by
    calc r * (x * Real.exp (-r * x)) = (r * x) * Real.exp (-r * x) := by ring
      _ ≤ Real.exp (r * x) * Real.exp (-r * x) :=
          mul_le_mul_of_nonneg_right h1 hpos.le
      _ = 1 := h2
  rw [inv_eq_one_div, le_div_iff₀ hr]
  linarith

private lemma laplace_to_complex_exp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hXmeas : AEMeasurable X P) (hXnn : ∀ᵐ ω ∂P, 0 ≤ X ω)
    (α tβ : ℝ) (hα : 0 < α)
    (hlap : ∀ q : ℝ, 0 ≤ q →
      ∫ ω, Real.exp (-q * X ω) ∂P = Real.exp (-tβ * Real.log (1 + q / α))) :
    ∀ z : ℂ, 0 ≤ z.re →
      ∫ ω, Complex.exp (-z * (X ω : ℂ)) ∂P =
        Complex.exp (-(tβ : ℂ) * Complex.log (1 + z / (α : ℂ))) := by
  let f : ℂ → ℂ := fun z => ∫ ω, Complex.exp (-z * (X ω : ℂ)) ∂P
  let g : ℂ → ℂ := fun z => Complex.exp (-(tβ : ℂ) * Complex.log (1 + z / (α : ℂ)))
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := by
    have hconv : Convex ℝ U := by
      intro x hx y hy a b ha hb hab
      change 0 < (a • x + b • y).re
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb1 : b = 1 := by linarith
        subst hb1; simp; exact hy
      · have : 0 < a * x.re := mul_pos ha' hx
        have : 0 ≤ b * y.re := mul_nonneg hb (le_of_lt hy)
        linarith
    exact hconv.isPreconnected
  have hf_diff : DifferentiableOn ℂ f U := by
    intro z₀ hz₀
    let r : ℝ := z₀.re / 2
    have hr : 0 < r := half_pos hz₀
    have hball_mem : Metric.ball z₀ r ∈ nhds z₀ := Metric.ball_mem_nhds z₀ hr
    have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (fun ω => Complex.exp (-z * (X ω : ℂ))) P :=
      fun z => ((Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable.comp_aemeasurable hXmeas).aestronglyMeasurable
    have hF_int : Integrable (fun ω => Complex.exp (-z₀ * (X ω : ℂ))) P := by
      refine Integrable.of_bound (hF_meas z₀) 1 ?_
      filter_upwards [hXnn] with ω hω
      exact exp_neg_mul_norm_le_one hz₀.le hω
    have hF'_meas : AEStronglyMeasurable
        (fun ω => -(X ω : ℂ) * Complex.exp (-z₀ * (X ω : ℂ))) P :=
      (((Complex.continuous_ofReal.neg.mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).measurable).comp_aemeasurable
        hXmeas).aestronglyMeasurable
    have hderiv_bd : ∀ᵐ ω ∂P, ∀ z ∈ Metric.ball z₀ r,
        ‖-(X ω : ℂ) * Complex.exp (-z * (X ω : ℂ))‖ ≤ r⁻¹ := by
      filter_upwards [hXnn] with ω hω z hz
      have hzre : r < z.re := by
        have hdist : ‖z - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
        have hre : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - z₀)
        have := (abs_lt.mp (lt_of_le_of_lt hre hdist)).1
        dsimp [r] at *; linarith
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hω,
        Complex.norm_exp]
      have hre : (-z * (X ω : ℂ)).re = -z.re * X ω := by simp
      rw [hre]
      calc X ω * Real.exp (-z.re * X ω)
          ≤ X ω * Real.exp (-r * X ω) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hω
            nlinarith
        _ ≤ r⁻¹ := mul_exp_neg_le_inv hr hω
    have hhasDeriv : ∀ᵐ ω ∂P, ∀ z ∈ Metric.ball z₀ r,
        HasDerivAt (fun w => Complex.exp (-w * (X ω : ℂ)))
          (-(X ω : ℂ) * Complex.exp (-z * (X ω : ℂ))) z := by
      refine Eventually.of_forall fun ω z _ => ?_
      have h1 : HasDerivAt (fun w : ℂ => -w * (X ω : ℂ)) (-(X ω : ℂ)) z := by
        simpa using (hasDerivAt_id z).neg.mul_const (X ω : ℂ)
      simpa [mul_comm] using h1.cexp
    have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hball_mem (Eventually.of_forall hF_meas) hF_int hF'_meas hderiv_bd
      (integrable_const r⁻¹) hhasDeriv
    exact hres.2.differentiableAt.differentiableWithinAt
  have hg_diff : DifferentiableOn ℂ g U := by
    intro z₀ hz₀
    have hslit : 1 + z₀ / (α : ℂ) ∈ Complex.slitPlane := by
      left
      simp only [add_re, one_re, div_ofReal_re]
      have : 0 < z₀.re / α := div_pos hz₀ hα
      linarith
    have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 + w / (α : ℂ)) z₀ :=
      (differentiableAt_const 1).add (differentiableAt_id.div_const (α : ℂ))
    have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.log (1 + w / (α : ℂ))) z₀ :=
      h1.clog hslit
    exact ((differentiableAt_const (-(tβ : ℂ))).mul h2).cexp.differentiableWithinAt
  have hreal_eq : ∀ q : ℝ, 0 < q → f (q : ℂ) = g (q : ℂ) := by
    intro q hq
    dsimp [f, g]
    have hrew : (fun ω => Complex.exp (-(q : ℂ) * (X ω : ℂ))) =
        fun ω => ((Real.exp (-q * X ω) : ℝ) : ℂ) := by
      funext ω
      rw [Complex.ofReal_exp]
      push_cast; rfl
    have hint_real : Integrable (fun ω => Real.exp (-q * X ω)) P := by
      refine Integrable.of_bound
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp_aemeasurable
          hXmeas).aestronglyMeasurable 1 ?_
      filter_upwards [hXnn] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    rw [hrew]
    change ∫ ω, Complex.ofRealCLM (Real.exp (-q * X ω)) ∂P = _
    rw [Complex.ofRealCLM.integral_comp_comm hint_real]
    change ((∫ ω, Real.exp (-q * X ω) ∂P : ℝ) : ℂ) = _
    rw [hlap q hq.le]
    have hpos : 0 < 1 + q / α := by positivity
    rw [Complex.ofReal_exp]
    congr 1
    rw [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_log hpos.le]
    push_cast; rfl
  have hfreq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, f z = g z := by
    rw [Filter.frequently_iff]
    intro s hs
    rw [mem_nhdsWithin] at hs
    obtain ⟨t, ht_open, h1t, hts⟩ := hs
    rw [Metric.isOpen_iff] at ht_open
    obtain ⟨ε, hε, hball⟩ := ht_open 1 h1t
    let q : ℝ := 1 + ε / 2
    have hq_pos : 0 < q := by positivity
    have hq_ne : (q : ℂ) ≠ 1 := by
      intro h
      have : q = 1 := Complex.ofReal_injective h
      dsimp [q] at this; linarith
    have hq_mem : (q : ℂ) ∈ t := by
      apply hball
      rw [Metric.mem_ball, Complex.dist_eq]
      have : (q : ℂ) - 1 = ((ε / 2 : ℝ) : ℂ) := by dsimp [q]; push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    exact ⟨(q : ℂ), hts ⟨hq_mem, hq_ne⟩, hreal_eq q hq_pos⟩
  have heqU : Set.EqOn f g U :=
    (hf_diff.analyticOnNhd hUopen).eqOn_of_preconnected_of_frequently_eq
      (hg_diff.analyticOnNhd hUopen) hUconn (by simp [U]) hfreq
  intro z hz
  let seq : ℕ → ℂ := fun n => z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hseq_U : ∀ n, seq n ∈ U := by
    intro n
    change 0 < (z + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)).re
    simp only [add_re, ofReal_re]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hseq_tendsto : Tendsto seq atTop (nhds z) := by
    have h0 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (nhds (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [seq] using (tendsto_const_nhds (x := z)).add h0
  have hf_tendsto : Tendsto (fun n => f (seq n)) atTop (nhds (f z)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
    · intro n
      exact (((Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable).comp_aemeasurable hXmeas).aestronglyMeasurable
    · intro n
      filter_upwards [hXnn] with ω hω
      exact exp_neg_mul_norm_le_one (hseq_U n).le hω
    · refine Eventually.of_forall fun ω => ?_
      have hc : Continuous (fun w : ℂ => Complex.exp (-w * (X ω : ℂ))) :=
        Complex.continuous_exp.comp (continuous_neg.mul continuous_const)
      exact (hc.tendsto z).comp hseq_tendsto
  have hg_tendsto : Tendsto (fun n => g (seq n)) atTop (nhds (g z)) := by
    have hslit : 1 + z / (α : ℂ) ∈ Complex.slitPlane := by
      left
      simp only [add_re, one_re, div_ofReal_re]
      have : 0 ≤ z.re / α := div_nonneg hz hα.le
      linarith
    have hcont : ContinuousAt g z := by
      have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 + w / (α : ℂ)) z :=
        (differentiableAt_const 1).add (differentiableAt_id.div_const (α : ℂ))
      have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.log (1 + w / (α : ℂ))) z :=
        h1.clog hslit
      exact ((differentiableAt_const (-(tβ : ℂ))).mul h2).cexp.continuousAt
    exact hcont.tendsto.comp hseq_tendsto
  have heq_seq : (fun n => f (seq n)) = fun n => g (seq n) :=
    funext fun n => heqU (hseq_U n)
  rw [heq_seq] at hf_tendsto
  exact tendsto_nhds_unique hf_tendsto hg_tendsto

/-! ### Section 4: Brownian Motion Joint CharFun & Subordination (Part 1) -/

private lemma measurable_exp_sum_diff {Ω : Type*} (m : MeasurableSpace Ω)
    {n : ℕ} (ξ : Fin n → ℝ) (W : Fin (n + 1) → Ω → ℝ)
    (hW : ∀ j, @Measurable Ω ℝ m _ (W j)) :
    @Measurable Ω ℂ m _ (fun ω => Complex.exp (∑ k : Fin n,
      Complex.I * (ξ k : ℂ) * ((W k.succ ω - W k.castSucc ω : ℝ) : ℂ))) := by
  let _ : MeasurableSpace Ω := m
  refine Complex.continuous_exp.measurable.comp ?_
  refine Finset.measurable_sum Finset.univ fun k _ => ?_
  exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp ((hW k.succ).sub (hW k.castSucc)))

private lemma brownian_joint_charFun {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P) :
    ∀ (n : ℕ) (u : Fin (n + 1) → ℝ) (_hu0 : 0 ≤ u 0) (_humono : Monotone u) (ξ : Fin n → ℝ),
      ∫ ω, Complex.exp (∑ k : Fin n,
          Complex.I * (ξ k : ℂ) * ((B.W (u k.succ) ω - B.W (u k.castSucc) ω : ℝ) : ℂ)) ∂P =
        ∏ k : Fin n, Complex.exp (-((u k.succ - u k.castSucc : ℝ) : ℂ) * ((ξ k : ℂ) ^ 2) / 2) := by
  intro n
  induction n with
  | zero =>
    intro u _ _ ξ
    simp
  | succ n ih =>
    intro u hu0 humono ξ
    let u' : Fin (n + 1) → ℝ := fun j => u j.castSucc
    let ξ' : Fin n → ℝ := fun k => ξ k.castSucc
    have hu'0 : 0 ≤ u' 0 := hu0
    have hu'mono : Monotone u' := fun a b hab => humono (Fin.castSucc_le_castSucc_iff.mpr hab)
    let s : ℝ := u (Fin.last n).castSucc
    let t : ℝ := u (Fin.last (n + 1))
    have hs0 : 0 ≤ s := le_trans hu0 (humono (Fin.zero_le _))
    have hst_le : s ≤ t := humono (Fin.le_last _)
    have hsplit : (fun ω => Complex.exp (∑ k : Fin (n + 1),
        Complex.I * (ξ k : ℂ) * ((B.W (u k.succ) ω - B.W (u k.castSucc) ω : ℝ) : ℂ))) =
        fun ω =>
          Complex.exp (∑ k : Fin n,
            Complex.I * (ξ' k : ℂ) * ((B.W (u' k.succ) ω - B.W (u' k.castSucc) ω : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (ξ (Fin.last n) : ℂ) * ((B.W t ω - B.W s ω : ℝ) : ℂ)) := by
      funext ω
      rw [Fin.sum_univ_castSucc, Complex.exp_add]
      rfl
    rw [hsplit, Fin.prod_univ_castSucc]
    rcases eq_or_lt_of_le hst_le with hst_eq | hst
    · have hzero : ∀ ω, B.W t ω - B.W s ω = 0 := fun ω => by rw [hst_eq, sub_self]
      have hsub0 : t - s = 0 := by rw [hst_eq, sub_self]
      simp only [hzero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
      change ∫ ω, Complex.exp (∑ k : Fin n,
          Complex.I * (ξ' k : ℂ) * ((B.W (u' k.succ) ω - B.W (u' k.castSucc) ω : ℝ) : ℂ)) ∂P =
        (∏ k : Fin n, Complex.exp (-((u' k.succ - u' k.castSucc : ℝ) : ℂ) * ((ξ' k : ℂ) ^ 2) / 2)) *
          Complex.exp (-((t - s : ℝ) : ℂ) * ((ξ (Fin.last n) : ℂ) ^ 2) / 2)
      rw [hsub0, Complex.ofReal_zero, neg_zero, zero_mul, zero_div, Complex.exp_zero, mul_one]
      exact ih u' hu'0 hu'mono ξ'
    · let F₁ : Ω → ℂ := fun ω => Complex.exp (∑ k : Fin n,
          Complex.I * (ξ' k : ℂ) * ((B.W (u' k.succ) ω - B.W (u' k.castSucc) ω : ℝ) : ℂ))
      let F₂ : Ω → ℂ := fun ω => Complex.exp (Complex.I * (ξ (Fin.last n) : ℂ) *
          ((B.W t ω - B.W s ω : ℝ) : ℂ))
      have hF₁_comap : MeasurableSpace.comap F₁ inferInstance ≤
          ⨆ j ∈ Set.Iic s, MeasurableSpace.comap (B.W j) inferInstance := by
        refine (measurable_exp_sum_diff
          (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (B.W j) inferInstance)
          ξ' (fun j => B.W (u' j)) fun j => ?_).comap_le
        have hj_le : u' j ∈ Set.Iic s := humono (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last j))
        have hle : MeasurableSpace.comap (B.W (u' j)) inferInstance ≤
            ⨆ r ∈ Set.Iic s, MeasurableSpace.comap (B.W r) inferInstance :=
          le_iSup₂_of_le (u' j) hj_le le_rfl
        intro S hS
        exact hle _ ⟨S, hS, rfl⟩
      have hF₂_comap : MeasurableSpace.comap F₂ inferInstance ≤
          MeasurableSpace.comap (fun ω => B.W t ω - B.W s ω) inferInstance := by
        refine (@Measurable.comp Ω ℝ ℂ
          (MeasurableSpace.comap (fun ω => B.W t ω - B.W s ω) inferInstance) _ _ _ _
          (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable
          (comap_measurable (fun ω => B.W t ω - B.W s ω))).comap_le
      have hind_F : IndepFun F₁ F₂ P := by
        have hind_m := B.joint_increment_independent hs0 hst
        exact indep_of_indep_of_le_left (indep_of_indep_of_le_right hind_m hF₂_comap) hF₁_comap
      have hF₁_meas : Measurable F₁ := by
        refine Complex.continuous_exp.measurable.comp ?_
        refine Finset.measurable_sum Finset.univ fun k _ => ?_
        exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          ((B.measurable_eval _).sub (B.measurable_eval _)))
      have hF₂_meas : Measurable F₂ :=
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable.comp
          ((B.measurable_eval t).sub (B.measurable_eval s))
      have hmul_int : ∫ ω, F₁ ω * F₂ ω ∂P = (∫ ω, F₁ ω ∂P) * (∫ ω, F₂ ω ∂P) :=
        hind_F.integral_fun_mul_eq_mul_integral hF₁_meas.aestronglyMeasurable hF₂_meas.aestronglyMeasurable
      have hF₂_val : ∫ ω, F₂ ω ∂P =
          Complex.exp (-((t - s : ℝ) : ℂ) * ((ξ (Fin.last n) : ℂ) ^ 2) / 2) := by
        have hdiff_meas : Measurable (fun ω => B.W t ω - B.W s ω) :=
          (B.measurable_eval t).sub (B.measurable_eval s)
        have hchar : ∫ ω, F₂ ω ∂P = charFun (P.map (fun ω => B.W t ω - B.W s ω)) (ξ (Fin.last n)) := by
          rw [charFun_apply_real, integral_map hdiff_meas.aemeasurable
            (f := fun x : ℝ => Complex.exp ((ξ (Fin.last n) : ℂ) * (x : ℂ) * Complex.I))
            (Complex.continuous_exp.comp
              ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable]
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          dsimp [F₂]; congr 1; ring
        rw [hchar, B.increment_gaussian hs0 hst]
        have hg : charFun (ProbabilityTheory.gaussianReal 0 (⟨t - s, by linarith⟩ : ℝ≥0))
            (ξ (Fin.last n)) =
            Complex.exp ((ξ (Fin.last n) : ℂ) * (0 : ℝ) * Complex.I -
              ((⟨t - s, by linarith⟩ : ℝ≥0) : ℝ) * (ξ (Fin.last n) : ℂ) ^ 2 / 2) :=
          charFun_gaussianReal (ξ (Fin.last n))
        rw [hg]
        simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
        congr 1; ring
      change ∫ ω, F₁ ω * F₂ ω ∂P =
        (∏ k : Fin n, Complex.exp (-((u' k.succ - u' k.castSucc : ℝ) : ℂ) * ((ξ' k : ℂ) ^ 2) / 2)) *
          Complex.exp (-((t - s : ℝ) : ℂ) * ((ξ (Fin.last n) : ℂ) ^ 2) / 2)
      rw [hmul_int, ih u' hu'0 hu'mono ξ', hF₂_val]

private noncomputable def dyadIdx (m : ℕ) (x : ℝ) : ℕ × ℕ :=
  (m, Nat.floor ((2 : ℝ) ^ m * max x 0))

private noncomputable def dyadVal (mk : ℕ × ℕ) : ℝ :=
  (mk.2 : ℝ) / (2 : ℝ) ^ mk.1

private lemma measurable_dyadIdx (m : ℕ) : Measurable (dyadIdx m) :=
  measurable_const.prodMk (Nat.measurable_floor.comp (measurable_const.mul (measurable_id.max measurable_const)))

private lemma measurable_eval_countable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {g : α → ι} (hg : Measurable g) :
    Measurable (fun p : (ι → β) × α => p.1 (g p.2)) := by
  intro S hS
  have hpre : (fun p : (ι → β) × α => p.1 (g p.2)) ⁻¹' S =
      ⋃ q : ι, ({f : ι → β | f q ∈ S} ×ˢ {x : α | g x = q}) := by
    ext ⟨f, x⟩
    simp
  rw [hpre]
  refine MeasurableSet.iUnion fun q => MeasurableSet.prod ?_ ?_
  · exact measurable_pi_apply q hS
  · exact hg (measurableSet_singleton q)

private lemma tendsto_dyadVal {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun m : ℕ => dyadVal (dyadIdx m x)) atTop (nhds x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with m hm
  have hmax : max x 0 = x := max_eq_left hx
  have hval : dyadVal (dyadIdx m x) = (Nat.floor ((2 : ℝ) ^ m * x) : ℝ) / (2 : ℝ) ^ m := by
    simp [dyadVal, dyadIdx, hmax]
  rw [Real.dist_eq, hval]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hle : (Nat.floor ((2 : ℝ) ^ m * x) : ℝ) ≤ (2 : ℝ) ^ m * x :=
    Nat.floor_le (mul_nonneg h2pos.le hx)
  have hlt : (2 : ℝ) ^ m * x < (Nat.floor ((2 : ℝ) ^ m * x) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hdiff_le : (Nat.floor ((2 : ℝ) ^ m * x) : ℝ) / (2 : ℝ) ^ m - x ≤ 0 := by
    rw [sub_nonpos, div_le_iff₀ h2pos]; linarith
  have hdiff_gt : -(1 / (2 : ℝ) ^ m) < (Nat.floor ((2 : ℝ) ^ m * x) : ℝ) / (2 : ℝ) ^ m - x := by
    have : ((Nat.floor ((2 : ℝ) ^ m * x) : ℝ) - (2 : ℝ) ^ m * x) / (2 : ℝ) ^ m =
        (Nat.floor ((2 : ℝ) ^ m * x) : ℝ) / (2 : ℝ) ^ m - x := by field_simp
    rw [← this, ← neg_div]
    exact div_lt_div_of_pos_right (by linarith) h2pos
  rw [abs_of_nonpos hdiff_le]
  have hpow : 1 / (2 : ℝ) ^ m = (1 / 2 : ℝ) ^ m := by rw [one_div_pow]
  linarith

private lemma levy_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : ℝ≥0 → Ω → ℝ}
    (hY : ProbabilityTheory.IsLevyProcess Y P) (t : ℝ≥0) :
    AEMeasurable (Y t) P := by
  have hid := hY.stationary_increments 0 t
  have heq : ProbabilityTheory.increment Y 0 (0 + t) = Y t := by
    funext ω
    simp [ProbabilityTheory.increment, hY.start_zero]
  rw [heq] at hid
  exact hid.aemeasurable_fst

private lemma subordinated_joint_charFun
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α β c σ : ℝ) (hα : 0 < α)
    (Γ : ℝ≥0 → Ω → ℝ≥0)
    (hΓlevy : ProbabilityTheory.IsLevyProcess (fun t ω => (Γ t ω : ℝ)) P)
    (hΓsub : ∀ᵐ ω ∂P, Monotone (fun t => Γ t ω))
    (hΓlaplace : ∀ (q : ℝ), 0 ≤ q → ∀ (t : ℝ≥0),
      ∫ ω, Real.exp (-q * (Γ t ω : ℝ)) ∂P =
        Real.exp (-(t : ℝ) * β * Real.log (1 + q / α)))
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hind : ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then B.W (t : ℝ) ω else (Γ t ω : ℝ)) P)
    {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) (ξ : Fin n → ℝ) :
    let X : ℝ≥0 → Ω → ℝ := fun s ω =>
      c * (Γ s ω : ℝ) + σ * (B.W (Γ s ω : ℝ) ω - B.W 0 ω)
    ∫ ω, Complex.exp (∑ k : Fin n,
        Complex.I * (ξ k : ℂ) * ((X (t k.succ) ω - X (t k.castSucc) ω : ℝ) : ℂ)) ∂P =
      ∏ k : Fin n, Complex.exp (-((((t k.succ - t k.castSucc : ℝ≥0) : ℝ) : ℂ)) * (β : ℂ) *
        Complex.log (1 - Complex.I * (((ξ k * c / α : ℝ) : ℂ)) +
          (((σ ^ 2 * (ξ k) ^ 2 / (2 * α) : ℝ) : ℂ)))) := by
  intro X
  let fB : Ω → (ℕ × ℕ → ℝ) := fun ω mk => B.W (dyadVal mk) ω
  let fΓ : Ω → (Fin (n + 1) → ℝ) := fun ω j => (Γ (t j) ω : ℝ)
  have hfB_meas : Measurable fB := measurable_pi_lambda _ fun mk => B.measurable_eval (dyadVal mk)
  have hfΓ_aemeas : AEMeasurable fΓ P :=
    aemeasurable_pi_lambda _ fun j => levy_aemeasurable hΓlevy (t j)
  have hind_pair : IndepFun fB fΓ P := by
    have h01 : IndepFun
        (fun ω (s : ℝ≥0) => B.W (s : ℝ) ω)
        (fun ω (s : ℝ≥0) => (Γ s ω : ℝ)) P := by
      have h := hind.indepFun (show (0 : Fin 2) ≠ 1 by decide)
      simpa using h
    have hprojB : Measurable (fun (g : ℝ≥0 → ℝ) (mk : ℕ × ℕ) =>
        g (⟨dyadVal mk, by dsimp [dyadVal]; positivity⟩ : ℝ≥0)) :=
      measurable_pi_lambda _ fun mk =>
        measurable_pi_apply (⟨dyadVal mk, by dsimp [dyadVal]; positivity⟩ : ℝ≥0)
    have hprojΓ : Measurable (fun (g : ℝ≥0 → ℝ) (j : Fin (n + 1)) => g (t j)) :=
      measurable_pi_lambda _ fun j => measurable_pi_apply (t j)
    exact h01.comp hprojB hprojΓ
  have hmap_prod : P.map (fun ω => (fB ω, fΓ ω)) = (P.map fB).prod (P.map fΓ) :=
    (indepFun_iff_map_prod_eq_prod_map_map hfB_meas.aemeasurable hfΓ_aemeas).mp hind_pair
  have : IsProbabilityMeasure (P.map fB) := Measure.isProbabilityMeasure_map hfB_meas.aemeasurable
  have : IsProbabilityMeasure (P.map fΓ) := Measure.isProbabilityMeasure_map hfΓ_aemeas
  let Fm : ℕ → (ℕ × ℕ → ℝ) × (Fin (n + 1) → ℝ) → ℂ := fun m p =>
    Complex.exp (∑ k : Fin n, Complex.I * (ξ k : ℂ) *
      ((c * (p.2 k.succ - p.2 k.castSucc) +
        σ * (p.1 (dyadIdx m (p.2 k.succ)) - p.1 (dyadIdx m (p.2 k.castSucc))) : ℝ) : ℂ))
  have hFm_meas : ∀ m, Measurable (Fm m) := fun m => by
    refine Complex.continuous_exp.measurable.comp ?_
    refine Finset.measurable_sum Finset.univ fun k _ => ?_
    refine measurable_const.mul (Complex.continuous_ofReal.measurable.comp ?_)
    have h1 : Measurable (fun p : (ℕ × ℕ → ℝ) × (Fin (n + 1) → ℝ) =>
        p.1 (dyadIdx m (p.2 k.succ))) :=
      measurable_eval_countable (g := fun u : Fin (n + 1) → ℝ => dyadIdx m (u k.succ))
        ((measurable_dyadIdx m).comp (measurable_pi_apply k.succ))
    have h2 : Measurable (fun p : (ℕ × ℕ → ℝ) × (Fin (n + 1) → ℝ) =>
        p.1 (dyadIdx m (p.2 k.castSucc))) :=
      measurable_eval_countable (g := fun u : Fin (n + 1) → ℝ => dyadIdx m (u k.castSucc))
        ((measurable_dyadIdx m).comp (measurable_pi_apply k.castSucc))
    exact (measurable_const.mul (((measurable_pi_apply k.succ).comp measurable_snd).sub
      ((measurable_pi_apply k.castSucc).comp measurable_snd))).add
      (measurable_const.mul (h1.sub h2))
  have hFm_norm : ∀ m p, ‖Fm m p‖ = 1 := fun m p => by
    dsimp [Fm]
    rw [Complex.norm_exp]
    have hre : (∑ k : Fin n, Complex.I * (ξ k : ℂ) *
        ((c * (p.2 k.succ - p.2 k.castSucc) +
          σ * (p.1 (dyadIdx m (p.2 k.succ)) - p.1 (dyadIdx m (p.2 k.castSucc))) : ℝ) : ℂ)).re = 0 := by
      rw [Complex.re_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      simp
    rw [hre, Real.exp_zero]
  have hX_diff : ∀ (k : Fin n) ω, X (t k.succ) ω - X (t k.castSucc) ω =
      c * ((Γ (t k.succ) ω : ℝ) - (Γ (t k.castSucc) ω : ℝ)) +
        σ * (B.W (Γ (t k.succ) ω : ℝ) ω - B.W (Γ (t k.castSucc) ω : ℝ) ω) := by
    intro k ω; dsimp [X]; ring
  -- Step 1: LHS is limit as m → ∞ of ∫ ω, Fm m (fB ω, fΓ ω) ∂P
  have htendsto_lhs : Tendsto (fun m => ∫ ω, Fm m (fB ω, fΓ ω) ∂P) atTop
      (nhds (∫ ω, Complex.exp (∑ k : Fin n,
        Complex.I * (ξ k : ℂ) * ((X (t k.succ) ω - X (t k.castSucc) ω : ℝ) : ℂ)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
    · intro m
      exact ((hFm_meas m).comp_aemeasurable (hfB_meas.aemeasurable.prodMk hfΓ_aemeas)).aestronglyMeasurable
    · intro m
      exact Eventually.of_forall fun ω => by rw [hFm_norm]
    · filter_upwards [B.continuous_paths] with ω hcont
      have hterm : ∀ k : Fin n, Tendsto (fun m => Complex.I * (ξ k : ℂ) *
          ((c * ((Γ (t k.succ) ω : ℝ) - (Γ (t k.castSucc) ω : ℝ)) +
            σ * (B.W (dyadVal (dyadIdx m (Γ (t k.succ) ω : ℝ))) ω -
              B.W (dyadVal (dyadIdx m (Γ (t k.castSucc) ω : ℝ))) ω) : ℝ) : ℂ)) atTop
          (nhds (Complex.I * (ξ k : ℂ) * ((X (t k.succ) ω - X (t k.castSucc) ω : ℝ) : ℂ))) := by
        intro k
        rw [hX_diff]
        have h1 : Tendsto (fun m => B.W (dyadVal (dyadIdx m (Γ (t k.succ) ω : ℝ))) ω) atTop
            (nhds (B.W (Γ (t k.succ) ω : ℝ) ω)) :=
          (hcont.tendsto _).comp (tendsto_dyadVal (NNReal.coe_nonneg _))
        have h2 : Tendsto (fun m => B.W (dyadVal (dyadIdx m (Γ (t k.castSucc) ω : ℝ))) ω) atTop
            (nhds (B.W (Γ (t k.castSucc) ω : ℝ) ω)) :=
          (hcont.tendsto _).comp (tendsto_dyadVal (NNReal.coe_nonneg _))
        have h3 := (tendsto_const_nhds (x := c * ((Γ (t k.succ) ω : ℝ) - (Γ (t k.castSucc) ω : ℝ)))).add
          ((tendsto_const_nhds (x := σ)).mul (h1.sub h2))
        exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp h3)
      exact (Complex.continuous_exp.tendsto _).comp (tendsto_finsetSum Finset.univ fun k _ => hterm k)
  -- Step 2: By independence + Fubini, ∫ ω, Fm m (fB ω, fΓ ω) ∂P = ∫ u, (∫ b, Fm m (b, u) ∂(P.map fB)) ∂(P.map fΓ)
  have hfubini : ∀ m, ∫ ω, Fm m (fB ω, fΓ ω) ∂P =
      ∫ u, (∫ b, Fm m (b, u) ∂(P.map fB)) ∂(P.map fΓ) := by
    intro m
    have hmap_int : ∫ ω, Fm m (fB ω, fΓ ω) ∂P = ∫ p, Fm m p ∂(P.map (fun ω => (fB ω, fΓ ω))) :=
      (integral_map (hfB_meas.aemeasurable.prodMk hfΓ_aemeas) (hFm_meas m).aestronglyMeasurable).symm
    rw [hmap_int, hmap_prod]
    have hint : Integrable (Fm m) ((P.map fB).prod (P.map fΓ)) :=
      Integrable.of_bound (hFm_meas m).aestronglyMeasurable 1
        (Eventually.of_forall fun p => by rw [hFm_norm])
    rw [integral_prod_symm _ hint]
  -- Step 3: For fixed monotone nonnegative u, inner integral → ∏ k, exp((I * ξ k * c - σ² * ξ k² / 2) * (u k.succ - u k.castSucc))
  let G : (Fin (n + 1) → ℝ) → ℂ := fun u =>
    ∏ k : Fin n, Complex.exp ((Complex.I * (ξ k : ℂ) * (c : ℂ) -
      ((σ : ℂ) ^ 2 * (ξ k : ℂ) ^ 2 / 2)) * ((u k.succ - u k.castSucc : ℝ) : ℂ))
  have hinner_tendsto : ∀ u : Fin (n + 1) → ℝ, 0 ≤ u 0 → Monotone u →
      Tendsto (fun m => ∫ b, Fm m (b, u) ∂(P.map fB)) atTop (nhds (G u)) := by
    intro u hu0 humono
    have hrew_m : ∀ m, ∫ b, Fm m (b, u) ∂(P.map fB) = ∫ ω, Fm m (fB ω, u) ∂P := fun m =>
      integral_map hfB_meas.aemeasurable
        ((hFm_meas m).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    simp_rw [hrew_m]
    have hlim_int : Tendsto (fun m => ∫ ω, Fm m (fB ω, u) ∂P) atTop
        (nhds (∫ ω, Complex.exp (∑ k : Fin n, Complex.I * (ξ k : ℂ) *
          ((c * (u k.succ - u k.castSucc) +
            σ * (B.W (u k.succ) ω - B.W (u k.castSucc) ω) : ℝ) : ℂ)) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
      · intro m
        exact ((hFm_meas m).comp (hfB_meas.prodMk measurable_const)).aestronglyMeasurable
      · intro m
        exact Eventually.of_forall fun ω => by rw [hFm_norm]
      · filter_upwards [B.continuous_paths] with ω hcont
        have hterm : ∀ k : Fin n, Tendsto (fun m => Complex.I * (ξ k : ℂ) *
            ((c * (u k.succ - u k.castSucc) +
              σ * (B.W (dyadVal (dyadIdx m (u k.succ))) ω -
                B.W (dyadVal (dyadIdx m (u k.castSucc))) ω) : ℝ) : ℂ)) atTop
            (nhds (Complex.I * (ξ k : ℂ) *
              ((c * (u k.succ - u k.castSucc) +
                σ * (B.W (u k.succ) ω - B.W (u k.castSucc) ω) : ℝ) : ℂ))) := by
          intro k
          have h1 : Tendsto (fun m => B.W (dyadVal (dyadIdx m (u k.succ))) ω) atTop
              (nhds (B.W (u k.succ) ω)) :=
            (hcont.tendsto _).comp (tendsto_dyadVal (le_trans hu0 (humono (Fin.zero_le _))))
          have h2 : Tendsto (fun m => B.W (dyadVal (dyadIdx m (u k.castSucc))) ω) atTop
              (nhds (B.W (u k.castSucc) ω)) :=
            (hcont.tendsto _).comp (tendsto_dyadVal (le_trans hu0 (humono (Fin.zero_le _))))
          have h3 := (tendsto_const_nhds (x := c * (u k.succ - u k.castSucc))).add
            ((tendsto_const_nhds (x := σ)).mul (h1.sub h2))
          exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp h3)
        exact (Complex.continuous_exp.tendsto _).comp (tendsto_finsetSum Finset.univ fun k _ => hterm k)
    have hval : ∫ ω, Complex.exp (∑ k : Fin n, Complex.I * (ξ k : ℂ) *
        ((c * (u k.succ - u k.castSucc) +
          σ * (B.W (u k.succ) ω - B.W (u k.castSucc) ω) : ℝ) : ℂ)) ∂P = G u := by
      have hpull : (fun ω => Complex.exp (∑ k : Fin n, Complex.I * (ξ k : ℂ) *
          ((c * (u k.succ - u k.castSucc) +
            σ * (B.W (u k.succ) ω - B.W (u k.castSucc) ω) : ℝ) : ℂ))) =
          fun ω =>
            Complex.exp (∑ k : Fin n, Complex.I * (ξ k : ℂ) * (c : ℂ) * ((u k.succ - u k.castSucc : ℝ) : ℂ)) *
            Complex.exp (∑ k : Fin n, Complex.I * ((σ * ξ k : ℝ) : ℂ) *
              ((B.W (u k.succ) ω - B.W (u k.castSucc) ω : ℝ) : ℂ)) := by
        funext ω
        rw [← Complex.exp_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast; ring
      rw [hpull, integral_const_mul, brownian_joint_charFun P B n u hu0 humono (fun k => σ * ξ k)]
      rw [Complex.exp_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Complex.exp_add]
      congr 1; push_cast; ring
    rwa [hval] at hlim_int
  -- Step 4: Outer DCT on P.map fΓ gives LHS = ∫ ω, G (fΓ ω) ∂P
  have houter_ae : ∀ᵐ u ∂(P.map fΓ), 0 ≤ u 0 ∧ Monotone u := by
    have hset : MeasurableSet {u : Fin (n + 1) → ℝ | 0 ≤ u 0 ∧ Monotone u} := by
      have h1 : MeasurableSet {u : Fin (n + 1) → ℝ | 0 ≤ u 0} :=
        measurableSet_le measurable_const (measurable_pi_apply 0)
      have h2 : {u : Fin (n + 1) → ℝ | Monotone u} =
          ⋂ a : Fin (n + 1), ⋂ b : Fin (n + 1), ⋂ (_ : a ≤ b), {u | u a ≤ u b} := by
        ext u; simp [Monotone]
      have h2m : MeasurableSet {u : Fin (n + 1) → ℝ | Monotone u} := by
        rw [h2]
        refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => MeasurableSet.iInter fun _ => ?_
        exact measurableSet_le (measurable_pi_apply a) (measurable_pi_apply b)
      exact h1.inter h2m
    rw [ae_iff]
    change (P.map fΓ) ({u : Fin (n + 1) → ℝ | 0 ≤ u 0 ∧ Monotone u}ᶜ) = 0
    rw [Measure.map_apply_of_aemeasurable hfΓ_aemeas hset.compl]
    have : {ω | fΓ ω ∉ {u : Fin (n + 1) → ℝ | 0 ≤ u 0 ∧ Monotone u}} ⊆
        {ω | ¬ Monotone (fun s => Γ s ω)} := by
      intro ω hω hmon
      apply hω
      refine ⟨NNReal.coe_nonneg _, fun a b hab => ?_⟩
      exact NNReal.coe_le_coe.mpr (hmon (ht hab))
    exact measure_mono_null this (ae_iff.mp hΓsub)
  have htendsto_rhs : Tendsto (fun m => ∫ u, (∫ b, Fm m (b, u) ∂(P.map fB)) ∂(P.map fΓ)) atTop
      (nhds (∫ u, G u ∂(P.map fΓ))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
    · intro m
      exact (StronglyMeasurable.integral_prod_left (hFm_meas m).stronglyMeasurable).aestronglyMeasurable
    · intro m
      refine Eventually.of_forall fun u => ?_
      calc ‖∫ b, Fm m (b, u) ∂(P.map fB)‖
          ≤ ∫ b, ‖Fm m (b, u)‖ ∂(P.map fB) := norm_integral_le_integral_norm _
        _ = 1 := by simp [hFm_norm]
    · filter_upwards [houter_ae] with u ⟨hu0, humono⟩
      exact hinner_tendsto u hu0 humono
  have hG_meas : Measurable G := by
    refine Finset.measurable_prod Finset.univ fun k _ => ?_
    exact Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        ((measurable_pi_apply k.succ).sub (measurable_pi_apply k.castSucc))))
  have hlhs_eq_G : ∫ ω, Complex.exp (∑ k : Fin n,
        Complex.I * (ξ k : ℂ) * ((X (t k.succ) ω - X (t k.castSucc) ω : ℝ) : ℂ)) ∂P =
      ∫ ω, G (fΓ ω) ∂P := by
    simp_rw [hfubini] at htendsto_lhs
    have h1 := tendsto_nhds_unique htendsto_lhs htendsto_rhs
    rw [h1, integral_map hfΓ_aemeas hG_meas.aestronglyMeasurable]
  rw [hlhs_eq_G]
  -- Step 5: Factor ∫ ω, G (fΓ ω) ∂P using hΓlevy.indep_increments, stationary_increments, laplace_to_complex_exp
  let Z : Fin n → Ω → ℂ := fun k ω =>
    Complex.exp ((Complex.I * (ξ k : ℂ) * (c : ℂ) - ((σ : ℂ) ^ 2 * (ξ k : ℂ) ^ 2 / 2)) *
      (((Γ (t k.succ) ω : ℝ) - (Γ (t k.castSucc) ω : ℝ) : ℝ) : ℂ))
  have hZ_indep : iIndepFun Z P := by
    have hindΓ := hΓlevy.indep_increments n t ht
    refine hindΓ.comp (fun k y => Complex.exp
      ((Complex.I * (ξ k : ℂ) * (c : ℂ) - ((σ : ℂ) ^ 2 * (ξ k : ℂ) ^ 2 / 2)) * (y : ℂ))) ?_
    intro k
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable
  have hZ_meas : ∀ k, AEStronglyMeasurable (Z k) P := fun k =>
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable.comp_aemeasurable
      ((levy_aemeasurable hΓlevy (t k.succ)).sub (levy_aemeasurable hΓlevy (t k.castSucc)))).aestronglyMeasurable
  have hfactor : ∫ ω, G (fΓ ω) ∂P = ∏ k : Fin n, ∫ ω, Z k ω ∂P := by
    have hrew : (fun ω => G (fΓ ω)) = ∏ k : Fin n, Z k := by
      funext ω; simp [G, Z, fΓ, Finset.prod_apply]
    rw [hrew]
    exact hZ_indep.integral_prod_eq_prod_integral hZ_meas
  rw [hfactor]
  refine Finset.prod_congr rfl fun k _ => ?_
  have htsub : t k.castSucc + (t k.succ - t k.castSucc) = t k.succ :=
    add_tsub_cancel_of_le (ht (Fin.castSucc_le_succ k))
  have hid := hΓlevy.stationary_increments (t k.castSucc) (t k.succ - t k.castSucc)
  rw [htsub] at hid
  let φ : ℝ → ℂ := fun y => Complex.exp
    ((Complex.I * (ξ k : ℂ) * (c : ℂ) - ((σ : ℂ) ^ 2 * (ξ k : ℂ) ^ 2 / 2)) * (y : ℂ))
  have hφ_cont : Continuous φ := Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hstat_int : ∫ ω, Z k ω ∂P =
      ∫ ω, φ ((Γ (t k.succ - t k.castSucc) ω : ℝ)) ∂P := by
    have h1 : (fun ω => Z k ω) = φ ∘ ProbabilityTheory.increment (fun s ω => (Γ s ω : ℝ)) (t k.castSucc) (t k.succ) := rfl
    have h2 : (fun ω => φ (Γ (t k.succ - t k.castSucc) ω : ℝ)) =
        φ ∘ ProbabilityTheory.increment (fun s ω => (Γ s ω : ℝ)) 0 (t k.succ - t k.castSucc) := by
      funext ω
      have h0 : (Γ 0 ω : ℝ) = 0 := congrFun hΓlevy.start_zero ω
      simp [ProbabilityTheory.increment, h0]
    rw [h1, h2]
    exact (hid.comp hφ_cont.measurable).integral_eq
  rw [hstat_int]
  let z : ℂ := ((σ : ℂ) ^ 2 * (ξ k : ℂ) ^ 2 / 2) - Complex.I * (ξ k : ℂ) * (c : ℂ)
  have hz_re : 0 ≤ z.re := by
    have hre : z.re = σ ^ 2 * (ξ k) ^ 2 / 2 := by
      dsimp [z]
      have hcast : ((σ : ℂ) ^ 2 * (ξ k : ℂ) ^ 2 / 2) = (((σ ^ 2 * (ξ k) ^ 2 / 2 : ℝ) : ℂ)) := by
        push_cast; rfl
      rw [hcast]
      simp only [ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, sub_zero, mul_zero]
    rw [hre]; positivity
  have hrew_z : (fun ω => φ (Γ (t k.succ - t k.castSucc) ω : ℝ)) =
      fun ω => Complex.exp (-z * ((Γ (t k.succ - t k.castSucc) ω : ℝ) : ℂ)) := by
    funext ω; dsimp [φ, z]; congr 1; ring
  rw [hrew_z, laplace_to_complex_exp P (fun ω => (Γ (t k.succ - t k.castSucc) ω : ℝ))
    (levy_aemeasurable hΓlevy _) (Eventually.of_forall fun ω => NNReal.coe_nonneg _)
    α (((t k.succ - t k.castSucc : ℝ≥0) : ℝ) * β) hα
    (fun q hq => by simpa [mul_assoc] using hΓlaplace q hq (t k.succ - t k.castSucc)) z hz_re]
  congr 1
  have hlog_arg : 1 + z / (α : ℂ) =
      1 - Complex.I * (((ξ k * c / α : ℝ) : ℂ)) + (((σ ^ 2 * (ξ k) ^ 2 / (2 * α) : ℝ) : ℂ)) := by
    dsimp [z]
    have hα_ne : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα.ne'
    push_cast
    field_simp [hα_ne]
    ring
  rw [hlog_arg]
  push_cast; ring

private lemma vg_charFun
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α β c σ : ℝ) (hα : 0 < α)
    (Γ : ℝ≥0 → Ω → ℝ≥0)
    (hΓlevy : ProbabilityTheory.IsLevyProcess (fun t ω => (Γ t ω : ℝ)) P)
    (hΓsub : ∀ᵐ ω ∂P, Monotone (fun t => Γ t ω))
    (hΓlaplace : ∀ (q : ℝ), 0 ≤ q → ∀ (t : ℝ≥0),
      ∫ ω, Real.exp (-q * (Γ t ω : ℝ)) ∂P =
        Real.exp (-(t : ℝ) * β * Real.log (1 + q / α)))
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hind : ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then B.W (t : ℝ) ω else (Γ t ω : ℝ)) P)
    (t : ℝ≥0) (ξ : ℝ) :
    let X : ℝ≥0 → Ω → ℝ := fun s ω =>
      c * (Γ s ω : ℝ) + σ * (B.W (Γ s ω : ℝ) ω - B.W 0 ω)
    charFun (P.map (X t)) ξ =
      Complex.exp (-(((t : ℝ) : ℂ)) * (β : ℂ) *
        Complex.log (1 - Complex.I * (((ξ * c / α : ℝ) : ℂ)) +
          (((σ ^ 2 * ξ ^ 2 / (2 * α) : ℝ) : ℂ)))) := by
  intro X
  have hX0 : ∀ ω, X 0 ω = 0 := fun ω => by
    have h0 : (Γ 0 ω : ℝ) = 0 := congrFun hΓlevy.start_zero ω
    simp [X, h0]
  have hX_aemeas : AEMeasurable (X t) P :=
    ((levy_aemeasurable hΓlevy t).const_mul c).add
      (((B.joint_measurable.comp_aemeasurable ((levy_aemeasurable hΓlevy t).prodMk aemeasurable_id)).sub
        (B.measurable_eval 0).aemeasurable).const_mul σ)
  let ts : Fin 2 → ℝ≥0 := ![0, t]
  have hts : Monotone ts := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [ts] at hab ⊢
  have hj := subordinated_joint_charFun P α β c σ hα Γ hΓlevy hΓsub hΓlaplace B hind ts hts ![ξ]
  rw [charFun_apply_real, integral_map hX_aemeas (f := fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I))
    (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable]
  have hlhs : ∫ ω, Complex.exp ((ξ : ℂ) * ((X t ω : ℝ) : ℂ) * Complex.I) ∂P =
      ∫ ω, Complex.exp (∑ k : Fin 1, Complex.I * ((![ξ] k : ℝ) : ℂ) *
        ((X (ts k.succ) ω - X (ts k.castSucc) ω : ℝ) : ℂ)) ∂P := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp [ts, hX0]
    congr 1; ring
  rw [hlhs, hj]
  simp [ts]

private lemma vg_isLevyProcess
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α β c σ : ℝ) (hα : 0 < α)
    (Γ : ℝ≥0 → Ω → ℝ≥0)
    (hΓlevy : ProbabilityTheory.IsLevyProcess (fun t ω => (Γ t ω : ℝ)) P)
    (hΓsub : ∀ᵐ ω ∂P, Monotone (fun t => Γ t ω))
    (hΓlaplace : ∀ (q : ℝ), 0 ≤ q → ∀ (t : ℝ≥0),
      ∫ ω, Real.exp (-q * (Γ t ω : ℝ)) ∂P =
        Real.exp (-(t : ℝ) * β * Real.log (1 + q / α)))
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hind : ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then B.W (t : ℝ) ω else (Γ t ω : ℝ)) P) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => c * (Γ t ω : ℝ) + σ * (B.W (Γ t ω : ℝ) ω - B.W 0 ω)) P := by
  let X : ℝ≥0 → Ω → ℝ := fun s ω =>
    c * (Γ s ω : ℝ) + σ * (B.W (Γ s ω : ℝ) ω - B.W 0 ω)
  have hX0 : X 0 = fun _ => 0 := by
    funext ω
    have h0 : (Γ 0 ω : ℝ) = 0 := congrFun hΓlevy.start_zero ω
    simp [X, h0]
  have hX_aemeas : ∀ s, AEMeasurable (X s) P := fun s =>
    ((levy_aemeasurable hΓlevy s).const_mul c).add
      (((B.joint_measurable.comp_aemeasurable ((levy_aemeasurable hΓlevy s).prodMk aemeasurable_id)).sub
        (B.measurable_eval 0).aemeasurable).const_mul σ)
  have hinc_char : ∀ s₁ s₂ : ℝ≥0, s₁ ≤ s₂ → ∀ ξ : ℝ,
      charFun (P.map (ProbabilityTheory.increment X s₁ s₂)) ξ =
        Complex.exp (-((((s₂ - s₁ : ℝ≥0) : ℝ) : ℂ)) * (β : ℂ) *
          Complex.log (1 - Complex.I * (((ξ * c / α : ℝ) : ℂ)) +
            (((σ ^ 2 * ξ ^ 2 / (2 * α) : ℝ) : ℂ)))) := by
    intro s₁ s₂ hle ξ
    let ts : Fin 2 → ℝ≥0 := ![s₁, s₂]
    have hts : Monotone ts := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp [ts, hle] at hab ⊢
    have hj := subordinated_joint_charFun P α β c σ hα Γ hΓlevy hΓsub hΓlaplace B hind ts hts ![ξ]
    have hinc_aemeas : AEMeasurable (ProbabilityTheory.increment X s₁ s₂) P :=
      (hX_aemeas s₂).sub (hX_aemeas s₁)
    rw [charFun_apply_real, integral_map hinc_aemeas
      (f := fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I))
      (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable]
    have hlhs : ∫ ω, Complex.exp ((ξ : ℂ) * ((ProbabilityTheory.increment X s₁ s₂ ω : ℝ) : ℂ) * Complex.I) ∂P =
        ∫ ω, Complex.exp (∑ k : Fin 1, Complex.I * ((![ξ] k : ℝ) : ℂ) *
          ((X (ts k.succ) ω - X (ts k.castSucc) ω : ℝ) : ℂ)) ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp [ts, ProbabilityTheory.increment]
      congr 1; ring
    rw [hlhs, hj]
    simp [ts]
  refine ⟨hX0, ?_, ?_, ?_⟩
  · -- HasIndependentIncrements
    intro n t ht
    refine iIndepFun_of_joint_charFun P
      (fun k => ProbabilityTheory.increment X (t k.castSucc) (t k.succ))
      (fun k => (hX_aemeas (t k.succ)).sub (hX_aemeas (t k.castSucc))) ?_
    intro ξ
    have hj := subordinated_joint_charFun P α β c σ hα Γ hΓlevy hΓsub hΓlaplace B hind t ht ξ
    simp only [ProbabilityTheory.increment]
    rw [hj]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact (hinc_char (t k.castSucc) (t k.succ) (ht (Fin.castSucc_le_succ k)) (ξ k)).symm
  · -- HasStationaryIncrements
    intro s h
    refine identDistrib_of_charFun P
      ((hX_aemeas (s + h)).sub (hX_aemeas s))
      ((hX_aemeas h).sub (hX_aemeas 0)) ?_
    intro ξ
    rw [hinc_char s (s + h) le_self_add ξ, hinc_char 0 h zero_le ξ]
    simp
  · -- cadlag_ae
    filter_upwards [hΓlevy.cadlag_ae, B.continuous_paths] with ω hΓcad hBcont
    intro t
    let g : ℝ → ℝ := fun y => c * y + σ * (B.W y ω - B.W 0 ω)
    have hg : Continuous g :=
      (continuous_const.mul continuous_id).add
        (continuous_const.mul (hBcont.sub continuous_const))
    obtain ⟨hrc, l, hlim⟩ := hΓcad t
    refine ⟨(hg.continuousAt.comp_continuousWithinAt hrc), g l, (hg.tendsto l).comp hlim⟩

/-! ### Section 5: Existence of a Gamma Subordinator via Poisson Random Measure -/

private lemma lintegral_poissonMeasure_id (r : ℝ≥0) :
    ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂(ProbabilityTheory.poissonMeasure r) = (r : ℝ≥0∞) := by
  unfold ProbabilityTheory.poissonMeasure
  rw [lintegral_sum_measure]
  have hterm : ∀ n : ℕ,
      ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂(ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) •
        Measure.dirac n) =
      ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) * (n : ℝ)) := by
    intro n
    rw [lintegral_smul_measure, lintegral_dirac' _ measurable_from_top, smul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  simp_rw [hterm]
  have hhasSum_real : HasSum (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) * (n : ℝ)) (r : ℝ) := by
    have hexp : HasSum (fun k : ℕ => (r : ℝ) ^ k / (k.factorial : ℝ)) (Real.exp (r : ℝ)) := by
      simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (r : ℝ)
    have hmul : HasSum (fun k : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) * ((r : ℝ) ^ k / (k.factorial : ℝ)))
        (Real.exp (-(r : ℝ)) * (r : ℝ) * Real.exp (r : ℝ)) :=
      hexp.mul_left (Real.exp (-(r : ℝ)) * (r : ℝ))
    have hval : Real.exp (-(r : ℝ)) * (r : ℝ) * Real.exp (r : ℝ) = (r : ℝ) := by
      have : Real.exp (-(r : ℝ)) * Real.exp (r : ℝ) = 1 := by rw [← Real.exp_add]; simp
      calc Real.exp (-(r : ℝ)) * (r : ℝ) * Real.exp (r : ℝ)
          = (r : ℝ) * (Real.exp (-(r : ℝ)) * Real.exp (r : ℝ)) := by ring
        _ = (r : ℝ) := by rw [this, mul_one]
    rw [hval] at hmul
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, sub_zero]
    refine hmul.congr_fun fun k => ?_
    rw [pow_succ, Nat.factorial_succ]
    push_cast
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hk]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hhasSum_real.summable,
    hhasSum_real.tsum_eq, ENNReal.ofReal_coe_nnreal]

private lemma prm_campbell_indicator
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) :
    ∫⁻ ω, N.N ω B ∂P = LevyStochCalc.Poisson.referenceIntensity ν B := by
  by_cases hfin : LevyStochCalc.Poisson.referenceIntensity ν B = ⊤
  · have hae := N.infinite_at_infinite_intensity hB hfin
    rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one, hfin]
  · have hlaw := N.poisson_law hB hfin
    have h1 : ∫⁻ ω, N.N ω B ∂P = ∫⁻ x : ℝ≥0∞, x ∂(P.map (fun ω => N.N ω B)) :=
      (lintegral_map measurable_id (N.measurable_eval hB)).symm
    rw [h1, hlaw]
    unfold LevyStochCalc.Poisson.poissonMeasureENN
    rw [lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id measurable_from_top]
    simpa [ENNReal.coe_toNNReal hfin] using
      lintegral_poissonMeasure_id (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal

private lemma prm_campbell_lintegral
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun ω => ∫⁻ z, f z ∂(N.N ω)) ∧
    ∫⁻ ω, (∫⁻ z, f z ∂(N.N ω)) ∂P =
      ∫⁻ z, f z ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
  have hsf : ∀ s : SimpleFunc (ℝ × ℝ) ℝ≥0∞,
      Measurable (fun ω => ∫⁻ z, s z ∂(N.N ω)) ∧
      ∫⁻ ω, (∫⁻ z, s z ∂(N.N ω)) ∂P =
        ∫⁻ z, s z ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
    intro s
    have hrep : ∀ μ : Measure (ℝ × ℝ), ∫⁻ z, s z ∂μ = ∑ c ∈ s.range, c * μ (s ⁻¹' {c}) :=
      fun μ => s.lintegral_eq_lintegral μ
    simp_rw [hrep]
    constructor
    · refine Finset.measurable_sum s.range fun c _ => ?_
      exact measurable_const.mul (N.measurable_eval (s.measurableSet_preimage {c}))
    · rw [lintegral_finsetSum]
      · refine Finset.sum_congr rfl fun c _ => ?_
        rw [lintegral_const_mul _ (N.measurable_eval (s.measurableSet_preimage {c})),
          prm_campbell_indicator P ν N (s.measurableSet_preimage {c})]
      · intro c _
        exact measurable_const.mul (N.measurable_eval (s.measurableSet_preimage {c}))
  have hsup : ∀ μ : Measure (ℝ × ℝ), ∫⁻ z, f z ∂μ = ⨆ n : ℕ, ∫⁻ z, SimpleFunc.eapprox f n z ∂μ := by
    intro μ
    rw [← lintegral_iSup (fun n => (SimpleFunc.eapprox f n).measurable)
      (fun a b hab z => SimpleFunc.monotone_eapprox f hab z)]
    congr 1; funext z
    exact (SimpleFunc.iSup_eapprox_apply hf z).symm
  simp_rw [hsup]
  constructor
  · exact Measurable.iSup fun n => (hsf (SimpleFunc.eapprox f n)).1
  · rw [lintegral_iSup (fun n => (hsf (SimpleFunc.eapprox f n)).1)
      (fun a b hab ω => lintegral_mono fun z => SimpleFunc.monotone_eapprox f hab z)]
    refine iSup_congr fun n => (hsf (SimpleFunc.eapprox f n)).2

private lemma integral_exp_neg_Ioi (a : ℝ) (ha : 0 < a) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) = a⁻¹ := by
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => -a⁻¹ * Real.exp (-a * y)) (Real.exp (-a * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -a * y) (-a) x := by
      simpa using (hasDerivAt_id x).const_mul (-a)
    have h2 := h1.exp.const_mul (-a⁻¹)
    have hval : -a⁻¹ * (Real.exp (-a * x) * -a) = Real.exp (-a * x) := by
      rw [mul_comm (Real.exp (-a * x)), ← mul_assoc, neg_mul_neg, inv_mul_cancel₀ ha.ne', one_mul]
    rwa [hval] at h2
  have hcont : ContinuousWithinAt (fun y : ℝ => -a⁻¹ * Real.exp (-a * y)) (Set.Ici 0) 0 :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousWithinAt
  have htend : Tendsto (fun y : ℝ => -a⁻¹ * Real.exp (-a * y)) atTop (nhds 0) := by
    have h1 : Tendsto (fun y : ℝ => -a * y) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr ha) tendsto_id
    simpa using (tendsto_const_nhds (x := -a⁻¹)).mul (Real.tendsto_exp_atBot.comp h1)
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Set.Ioi 0) volume := by
    have h := integrableOn_exp_mul_Ioi (a := -a) (by linarith) (0 : ℝ)
    simpa using h
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend]
  simp

private noncomputable def gammaLevyDensity (α' β x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (if 0 < x then β * x⁻¹ * Real.exp (-α' * x) else 0)

private lemma measurable_gammaLevyDensity (α' β : ℝ) :
    Measurable (gammaLevyDensity α' β) :=
  ENNReal.measurable_ofReal.comp
    (Measurable.ite (measurableSet_lt measurable_const measurable_id)
      ((measurable_const.mul measurable_inv).mul
        (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)))
      measurable_const)

private noncomputable def gammaLevyMeasure (α' β : ℝ) : Measure ℝ :=
  volume.withDensity (gammaLevyDensity α' β)

private lemma gammaLevyMeasure_Ioi_lt_top (α' β δ : ℝ) (hα' : 0 < α') (hβ : 0 < β) (hδ : 0 < δ) :
    gammaLevyMeasure α' β (Set.Ioi δ) < ⊤ := by
  unfold gammaLevyMeasure
  rw [withDensity_apply _ measurableSet_Ioi]
  have hle : ∫⁻ x in Set.Ioi δ, gammaLevyDensity α' β x ≤
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal ((β / δ) * Real.exp (-α' * x)) := by
    calc ∫⁻ x in Set.Ioi δ, gammaLevyDensity α' β x
        ≤ ∫⁻ x in Set.Ioi δ, ENNReal.ofReal ((β / δ) * Real.exp (-α' * x)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hx0 : 0 < x := lt_trans hδ hx
          simp only [gammaLevyDensity, if_pos hx0]
          refine ENNReal.ofReal_le_ofReal ?_
          have hinv : x⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ hx0 hδ).mpr hx.le
          have h1 : β * x⁻¹ ≤ β / δ := by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hinv hβ.le
          exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal ((β / δ) * Real.exp (-α' * x)) :=
          lintegral_mono_set (Set.Ioi_subset_Ioi hδ.le)
  refine lt_of_le_of_lt hle ?_
  have hint : IntegrableOn (fun x : ℝ => (β / δ) * Real.exp (-α' * x)) (Set.Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (a := -α') (by linarith) (0 : ℝ)).const_mul (β / δ)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x => by positivity)]
  exact ENNReal.ofReal_lt_top

private lemma sigmaFinite_gammaLevyMeasure (α' β : ℝ) (hα' : 0 < α') (hβ : 0 < β) :
    SigmaFinite (gammaLevyMeasure α' β) := by
  let s : ℕ → Set ℝ := fun n => if n = 0 then Set.Iic 0 else Set.Ioi (1 / (n : ℝ))
  refine ⟨⟨⟨s, fun n => ?_, fun n => ?_, ?_⟩⟩⟩
  · by_cases hn : n = 0
    · simp [s, hn]
    · simp [s, hn]
  · by_cases hn : n = 0
    · simp only [s, if_pos hn, gammaLevyMeasure, withDensity_apply _ measurableSet_Iic]
      have h0 : ∫⁻ x in Set.Iic (0 : ℝ), gammaLevyDensity α' β x = 0 := by
        refine setLIntegral_eq_zero measurableSet_Iic fun x hx => ?_
        have hnot : ¬ (0 < x) := not_lt.mpr hx
        simp [gammaLevyDensity, hnot]
      rw [h0]; exact ENNReal.zero_lt_top
    · simp only [s, if_neg hn]
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      exact gammaLevyMeasure_Ioi_lt_top α' β (1 / (n : ℝ)) hα' hβ (by positivity)
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x ≤ 0
    · exact ⟨0, by simp [s, hx]⟩
    · push Not at hx
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / x)
      refine ⟨n + 1, ?_⟩
      simp only [s, Nat.succ_ne_zero, ↓reduceIte, Set.mem_Ioi]
      push_cast
      have h1 : 1 / x < (n : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      rw [div_lt_iff₀ hx] at h1
      linarith

private lemma gammaLevyMeasure_first_moment (α' β : ℝ) (hα' : 0 < α') (hβ : 0 < β) :
    ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal x ∂(gammaLevyMeasure α' β) =
      ENNReal.ofReal (β / α') := by
  unfold gammaLevyMeasure
  rw [setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_gammaLevyDensity α' β)
    ENNReal.measurable_ofReal measurableSet_Ioi]
  have hcongr : ∫⁻ x in Set.Ioi (0 : ℝ), (gammaLevyDensity α' β * fun x => ENNReal.ofReal x) x =
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (β * Real.exp (-α' * x)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hxpos : 0 < x := hx
    simp only [Pi.mul_apply, gammaLevyDensity, if_pos hxpos]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hxne : x ≠ 0 := hxpos.ne'
    field_simp [hxne]
  rw [hcongr]
  have hint : IntegrableOn (fun x : ℝ => β * Real.exp (-α' * x)) (Set.Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (a := -α') (by linarith) (0 : ℝ)).const_mul β
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => by positivity),
    integral_const_mul, integral_exp_neg_Ioi α' hα', div_eq_mul_inv]

private lemma frullani_real (α' q : ℝ) (hα' : 0 < α') (hq : 0 ≤ q) :
    ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x) =
      Real.log (1 + q / α') := by
  have hfub := lintegral_lintegral_swap
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := volume.restrict (Set.Ioc α' (α' + q)))
    (f := fun x s : ℝ => ENNReal.ofReal (Real.exp (-s * x)))
    (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_snd.neg.mul measurable_fst))).aemeasurable
  have hlhs_inner : ∀ x ∈ Set.Ioi (0 : ℝ),
      ∫⁻ s in Set.Ioc α' (α' + q), ENNReal.ofReal (Real.exp (-s * x)) =
        ENNReal.ofReal ((1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x)) := by
    intro x hx
    have hint_s : IntegrableOn (fun s : ℝ => Real.exp (-s * x)) (Set.Ioc α' (α' + q)) volume :=
      (Real.continuous_exp.comp (continuous_neg.mul continuous_const)).continuousOn.integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint_s (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    congr 1
    rw [← intervalIntegral.integral_of_le (by linarith : α' ≤ α' + q)]
    have hderiv : ∀ s ∈ Set.uIcc α' (α' + q),
        HasDerivAt (fun y : ℝ => -x⁻¹ * Real.exp (-y * x)) (Real.exp (-s * x)) s := by
      intro s _
      have h1 : HasDerivAt (fun y : ℝ => -y * x) (-x) s := by
        simpa using (hasDerivAt_id s).neg.mul_const x
      have h2 := h1.exp.const_mul (-x⁻¹)
      have hxpos : 0 < x := hx
      have hval : -x⁻¹ * (Real.exp (-s * x) * -x) = Real.exp (-s * x) := by
        rw [mul_comm (Real.exp (-s * x)), ← mul_assoc, neg_mul_neg, inv_mul_cancel₀ hxpos.ne', one_mul]
      rwa [hval] at h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Real.continuous_exp.comp (continuous_neg.mul continuous_const)).intervalIntegrable _ _)]
    have hexp_add : Real.exp (-(α' + q) * x) = Real.exp (-q * x) * Real.exp (-α' * x) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp_add]; ring
  have hrhs_inner : ∀ s ∈ Set.Ioc α' (α' + q),
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s * x)) = ENNReal.ofReal s⁻¹ := by
    intro s hs
    have hs_pos : 0 < s := lt_trans hα' hs.1
    have hint_x : IntegrableOn (fun x : ℝ => Real.exp (-s * x)) (Set.Ioi 0) volume :=
      integrableOn_exp_mul_Ioi (a := -s) (by linarith) (0 : ℝ)
    rw [← ofReal_integral_eq_lintegral_ofReal hint_x (Eventually.of_forall fun _ => (Real.exp_pos _).le),
      integral_exp_neg_Ioi s hs_pos]
  have h1 : ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x)) =
      ∫⁻ s in Set.Ioc α' (α' + q), ENNReal.ofReal s⁻¹ := by
    calc ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x))
        = ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ s in Set.Ioc α' (α' + q), ENNReal.ofReal (Real.exp (-s * x)) :=
          (setLIntegral_congr_fun measurableSet_Ioi hlhs_inner).symm
      _ = ∫⁻ s in Set.Ioc α' (α' + q), ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s * x)) := hfub
      _ = ∫⁻ s in Set.Ioc α' (α' + q), ENNReal.ofReal s⁻¹ :=
          setLIntegral_congr_fun measurableSet_Ioc hrhs_inner
  have h2 : ∫⁻ s in Set.Ioc α' (α' + q), ENNReal.ofReal s⁻¹ = ENNReal.ofReal (Real.log (1 + q / α')) := by
    have hcont_inv : ContinuousOn (fun s : ℝ => s⁻¹) (Set.Icc α' (α' + q)) :=
      continuousOn_inv₀.mono fun s hs => ne_of_gt (lt_of_lt_of_le hα' hs.1)
    have hint_inv : IntegrableOn (fun s : ℝ => s⁻¹) (Set.Ioc α' (α' + q)) volume :=
      hcont_inv.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint_inv]
    · congr 1
      rw [← intervalIntegral.integral_of_le (by linarith : α' ≤ α' + q)]
      have hderiv : ∀ s ∈ Set.uIcc α' (α' + q), HasDerivAt Real.log s⁻¹ s := by
        intro s hs
        rw [Set.uIcc_of_le (by linarith : α' ≤ α' + q)] at hs
        exact Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le hα' hs.1))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (hcont_inv.intervalIntegrable_of_Icc (by linarith : α' ≤ α' + q))]
      rw [← Real.log_div (by linarith) hα'.ne']
      congr 1; field_simp [hα'.ne']
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact inv_nonneg.mpr (lt_trans hα' hs.1).le
  have hnn : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      0 ≤ (1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    have h1le : Real.exp (-q * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have : 0 ≤ 1 - Real.exp (-q * x) := by linarith
    positivity
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (((measurable_const.sub (Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id))).mul measurable_inv).mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  have hint_lhs : IntegrableOn (fun x : ℝ => (1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x))
      (Set.Ioi (0 : ℝ)) volume := by
    refine ⟨hmeas, ?_⟩
    rw [HasFiniteIntegral]
    have hcongr : ∫⁻ x in Set.Ioi (0 : ℝ), ‖(1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x)‖ₑ =
        ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hnn] with x hx
      rw [Real.enorm_eq_ofReal hx]
    rw [hcongr, h1, h2]
    exact ENNReal.ofReal_lt_top
  have heq_ofReal : ENNReal.ofReal (∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x)) =
      ENNReal.ofReal (Real.log (1 + q / α')) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_lhs hnn, h1, h2]
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hnn)
    (Real.log_nonneg (by have : 0 ≤ q / α' := div_nonneg hq hα'.le; linarith))).mp heq_ofReal

private lemma norm_one_sub_cexp_le {z : ℂ} (hz : 0 ≤ z.re) :
    ‖1 - Complex.exp (-z)‖ ≤ ‖z‖ := by
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => 1 - Complex.exp ((-z) * (s : ℂ))) (z * Complex.exp ((-z) * (t : ℂ))) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (-z) * (s : ℂ)) (-z) t := by
      have hcast : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      simpa using hcast.const_mul (-z)
    have h2 := h1.cexp.const_sub (1 : ℂ)
    have hval : -(Complex.exp ((-z) * (t : ℂ)) * -z) = z * Complex.exp ((-z) * (t : ℂ)) := by ring
    rwa [hval] at h2
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => 1 - Complex.exp ((-z) * (s : ℂ)))
    (f' := fun s : ℝ => z * Complex.exp ((-z) * (s : ℂ)))
    (s := Set.Icc 0 1) (C := ‖z‖)
    (fun t ht => (hderiv t ht).hasDerivWithinAt)
    (fun t ht => by
      rw [norm_mul, Complex.norm_exp]
      have hre : ((-z) * (t : ℂ)).re = -t * z.re := by simp; ring
      rw [hre]
      have hexp : Real.exp (-t * z.re) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
      calc ‖z‖ * Real.exp (-t * z.re) ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ = ‖z‖ := mul_one _)
    (convex_Icc 0 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  simpa using hmvt

private lemma frullani_complex (α' β ξ : ℝ) (hα' : 0 < α') (hβ : 0 < β) :
    ∫ x in Set.Ioi (0 : ℝ), (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂(gammaLevyMeasure α' β) =
      -(β : ℂ) * Complex.log (1 - Complex.I * (((ξ / α' : ℝ) : ℂ))) := by
  let F : ℂ → ℂ := fun z =>
    ∫ x in Set.Ioi (0 : ℝ), (1 - Complex.exp (-z * (x : ℂ))) *
      (((β * x⁻¹ * Real.exp (-α' * x) : ℝ) : ℂ))
  let G : ℂ → ℂ := fun z => (β : ℂ) * Complex.log (1 + z / (α' : ℂ))
  let V : Set ℂ := {z : ℂ | -α' < z.re}
  have hVopen : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVconn : IsPreconnected V := by
    have hconv : Convex ℝ V := by
      intro x hx y hy a b ha hb hab
      change -α' < (a • x + b • y).re
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      change -α' < x.re at hx
      change -α' < y.re at hy
      rcases ha.eq_or_lt with rfl | ha' <;> nlinarith
    exact hconv.isPreconnected
  have hF_integrable : ∀ z ∈ V, IntegrableOn
      (fun x : ℝ => (1 - Complex.exp (-z * (x : ℂ))) * (((β * x⁻¹ * Real.exp (-α' * x) : ℝ) : ℂ)))
      (Set.Ioi 0) volume := by
    intro z hz
    change -α' < z.re at hz
    let a : ℝ := min α' (α' + z.re)
    have ha : 0 < a := lt_min hα' (by linarith)
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ => (1 - Complex.exp (-z * (x : ℂ))) * (((β * x⁻¹ * Real.exp (-α' * x) : ℝ) : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      ((measurable_const.sub (Complex.continuous_exp.measurable.comp
        (measurable_const.mul Complex.continuous_ofReal.measurable))).mul
        (Complex.continuous_ofReal.measurable.comp
          (((measurable_const.mul measurable_inv).mul
            (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)))))).aestronglyMeasurable
    have hdom : IntegrableOn (fun x : ℝ => ‖z‖ * β * Real.exp (-a * x)) (Set.Ioi 0) volume :=
      (integrableOn_exp_mul_Ioi (a := -a) (by linarith) (0 : ℝ)).const_mul (‖z‖ * β)
    refine hdom.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hbd1 : ‖1 - Complex.exp (-z * (x : ℂ))‖ ≤ ‖z‖ * x * Real.exp (max 0 (-z.re) * x) := by
      have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (fun s : ℝ => 1 - Complex.exp ((-z * (x : ℂ)) * (s : ℂ)))
            ((z * (x : ℂ)) * Complex.exp ((-z * (x : ℂ)) * (t : ℂ))) t := by
        intro t _
        have h1 : HasDerivAt (fun s : ℝ => (-z * (x : ℂ)) * (s : ℂ)) (-z * (x : ℂ)) t := by
          have hcast : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
          simpa using hcast.const_mul (-z * (x : ℂ))
        have h2 := h1.cexp.const_sub (1 : ℂ)
        have hval : -(Complex.exp ((-z * (x : ℂ)) * (t : ℂ)) * (-z * (x : ℂ))) =
            (z * (x : ℂ)) * Complex.exp ((-z * (x : ℂ)) * (t : ℂ)) := by ring
        rwa [hval] at h2
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun s : ℝ => 1 - Complex.exp ((-z * (x : ℂ)) * (s : ℂ)))
        (f' := fun s : ℝ => (z * (x : ℂ)) * Complex.exp ((-z * (x : ℂ)) * (s : ℂ)))
        (s := Set.Icc 0 1) (C := ‖z‖ * x * Real.exp (max 0 (-z.re) * x))
        (fun t ht => (hderiv t ht).hasDerivWithinAt)
        (fun t ht => by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos, Complex.norm_exp]
          have hre : ((-z * (x : ℂ)) * (t : ℂ)).re = t * (-z.re) * x := by simp; ring
          rw [hre]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          have hmax : -z.re ≤ max 0 (-z.re) := le_max_right _ _
          have hmax0 : 0 ≤ max 0 (-z.re) := le_max_left _ _
          have ht1 : t * (-z.re) ≤ t * max 0 (-z.re) := mul_le_mul_of_nonneg_left hmax ht.1
          have ht2 : t * max 0 (-z.re) ≤ 1 * max 0 (-z.re) := mul_le_mul_of_nonneg_right ht.2 hmax0
          nlinarith)
        (convex_Icc 0 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
      simpa using hmvt
    have hmul : ‖1 - Complex.exp (-z * (x : ℂ))‖ * (β * x⁻¹ * Real.exp (-α' * x)) ≤
        ‖z‖ * β * (Real.exp (max 0 (-z.re) * x) * Real.exp (-α' * x)) := by
      have h1 := mul_le_mul_of_nonneg_right hbd1 (by positivity : 0 ≤ β * x⁻¹ * Real.exp (-α' * x))
      have hsimp : ‖z‖ * x * Real.exp (max 0 (-z.re) * x) * (β * x⁻¹ * Real.exp (-α' * x)) =
          ‖z‖ * β * (Real.exp (max 0 (-z.re) * x) * Real.exp (-α' * x)) := by
        have hxne : x ≠ 0 := hxpos.ne'
        field_simp [hxne]
      linarith
    have hexp_le : Real.exp (max 0 (-z.re) * x) * Real.exp (-α' * x) ≤ Real.exp (-a * x) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have : max 0 (-z.re) - α' = -a := by
        dsimp [a]
        rcases le_or_gt 0 (-z.re) with hle | hgt
        · rw [max_eq_right hle, min_eq_right (by linarith)]; ring
        · rw [max_eq_left hgt.le, min_eq_left (by linarith)]; ring
      nlinarith
    exact le_trans hmul (mul_le_mul_of_nonneg_left hexp_le (by positivity))
  have hF_diff : DifferentiableOn ℂ F V := by
    intro z₀ hz₀
    change -α' < z₀.re at hz₀
    let r : ℝ := (z₀.re + α') / 2
    have hr : 0 < r := half_pos (by linarith)
    have hball_mem : Metric.ball z₀ r ∈ nhds z₀ := Metric.ball_mem_nhds z₀ hr
    have hF_meas : ∀ z : ℂ, AEStronglyMeasurable
        (fun x : ℝ => (1 - Complex.exp (-z * (x : ℂ))) * (((β * x⁻¹ * Real.exp (-α' * x) : ℝ) : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) := fun z =>
      ((measurable_const.sub (Complex.continuous_exp.measurable.comp
        (measurable_const.mul Complex.continuous_ofReal.measurable))).mul
        (Complex.continuous_ofReal.measurable.comp
          (((measurable_const.mul measurable_inv).mul
            (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)))))).aestronglyMeasurable
    have hF'_meas : AEStronglyMeasurable
        (fun x : ℝ => (β : ℂ) * Complex.exp (-(z₀ + (α' : ℂ)) * (x : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (measurable_const.mul (Complex.continuous_exp.measurable.comp
        (measurable_const.mul Complex.continuous_ofReal.measurable))).aestronglyMeasurable
    have hderiv_bd : ∀ᵐ (x : ℝ) ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ z ∈ Metric.ball z₀ r,
        ‖(β : ℂ) * Complex.exp (-(z + (α' : ℂ)) * (x : ℂ))‖ ≤ β * Real.exp (-r * x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
      have hxpos : 0 < x := hx
      have hzre : r < z.re + α' := by
        have hdist : ‖z - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
        have hre : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (z - z₀)
        have := (abs_lt.mp (lt_of_le_of_lt hre hdist)).1
        dsimp [r] at *; linarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ, Complex.norm_exp]
      have hre : (-(z + (α' : ℂ)) * (x : ℂ)).re = -(z.re + α') * x := by simp
      rw [hre]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hβ.le
    have hhasDeriv : ∀ᵐ (x : ℝ) ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ z ∈ Metric.ball z₀ r,
        HasDerivAt (fun w : ℂ => (1 - Complex.exp (-w * (x : ℂ))) *
            (((β * x⁻¹ * Real.exp (-α' * x) : ℝ) : ℂ)))
          ((β : ℂ) * Complex.exp (-(z + (α' : ℂ)) * (x : ℂ))) z := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z _
      have hxpos : 0 < x := hx
      have h1 : HasDerivAt (fun w : ℂ => -w * (x : ℂ)) (-(x : ℂ)) z := by
        simpa using (hasDerivAt_id z).neg.mul_const (x : ℂ)
      have h2 := (h1.cexp.const_sub (1 : ℂ)).mul_const
        (((β * x⁻¹ * Real.exp (-α' * x) : ℝ) : ℂ))
      have hval : -(Complex.exp (-z * (x : ℂ)) * -(x : ℂ)) * (((β * x⁻¹ * Real.exp (-α' * x) : ℝ) : ℂ)) =
          (β : ℂ) * Complex.exp (-(z + (α' : ℂ)) * (x : ℂ)) := by
        have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
        have hexp : Complex.exp (-(z + (α' : ℂ)) * (x : ℂ)) =
            Complex.exp (-z * (x : ℂ)) * ((Real.exp (-α' * x) : ℝ) : ℂ) := by
          rw [Complex.ofReal_exp, ← Complex.exp_add]
          congr 1; push_cast; ring
        rw [hexp]
        push_cast
        field_simp [hxne]
      rwa [hval] at h2
    have hbd_int : IntegrableOn (fun x : ℝ => β * Real.exp (-r * x)) (Set.Ioi (0 : ℝ)) volume :=
      (integrableOn_exp_mul_Ioi (a := -r) (by linarith) (0 : ℝ)).const_mul β
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun (z : ℂ) (x : ℝ) => (1 - Complex.exp (-z * (x : ℂ))) * (((β * x⁻¹ * Real.exp (-α' * x) : ℝ) : ℂ)))
      (F' := fun (z : ℂ) (x : ℝ) => (β : ℂ) * Complex.exp (-(z + (α' : ℂ)) * (x : ℂ)))
      hball_mem (Eventually.of_forall hF_meas) (hF_integrable z₀ hz₀) hF'_meas
      hderiv_bd hbd_int hhasDeriv).2.differentiableAt.differentiableWithinAt
  have hG_diff : DifferentiableOn ℂ G V := by
    intro z₀ hz₀
    change -α' < z₀.re at hz₀
    have hslit : 1 + z₀ / (α' : ℂ) ∈ Complex.slitPlane := by
      left
      simp only [add_re, one_re, div_ofReal_re]
      have : -1 < z₀.re / α' := by rw [lt_div_iff₀ hα']; linarith
      linarith
    have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 + w / (α' : ℂ)) z₀ :=
      (differentiableAt_const 1).add (differentiableAt_id.div_const (α' : ℂ))
    exact ((differentiableAt_const (β : ℂ)).mul (h1.clog hslit)).differentiableWithinAt
  have hreal_eq : ∀ q : ℝ, 0 < q → F (q : ℂ) = G (q : ℂ) := by
    intro q hq
    dsimp [F, G]
    have hrew : (fun x : ℝ => (1 - Complex.exp (-(q : ℂ) * (x : ℂ))) *
        (((β * x⁻¹ * Real.exp (-α' * x) : ℝ) : ℂ))) =
        fun x : ℝ => Complex.ofRealCLM (β * ((1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x))) := by
      funext x
      change _ = (((β * ((1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x)) : ℝ) : ℂ))
      rw [show -(q : ℂ) * (x : ℂ) = (((-q * x : ℝ) : ℂ)) by push_cast; ring, ← Complex.ofReal_exp]
      push_cast; ring
    have hint_real : IntegrableOn
        (fun x : ℝ => β * ((1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x))) (Set.Ioi 0) volume := by
      have h1 := hF_integrable (q : ℂ) (by change -α' < q; linarith)
      rw [hrew] at h1
      have hre := Complex.reCLM.integrable_comp h1
      refine hre.congr (Eventually.of_forall fun x => ?_)
      change Complex.re (((β * ((1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x)) : ℝ) : ℂ)) = _
      exact Complex.ofReal_re _
    rw [hrew, Complex.ofRealCLM.integral_comp_comm hint_real]
    change ((∫ x in Set.Ioi (0 : ℝ), β * ((1 - Real.exp (-q * x)) * x⁻¹ * Real.exp (-α' * x)) : ℝ) : ℂ) = _
    rw [integral_const_mul, frullani_real α' q hα' hq.le]
    have hpos : 0 < 1 + q / α' := by positivity
    rw [Complex.ofReal_mul, Complex.ofReal_log hpos.le]
    push_cast; rfl
  have hfreq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, F z = G z := by
    rw [Filter.frequently_iff]
    intro s hs
    rw [mem_nhdsWithin] at hs
    obtain ⟨t, ht_open, h1t, hts⟩ := hs
    rw [Metric.isOpen_iff] at ht_open
    obtain ⟨ε, hε, hball⟩ := ht_open 1 h1t
    let q : ℝ := 1 + ε / 2
    have hq_pos : 0 < q := by positivity
    have hq_ne : (q : ℂ) ≠ 1 := by
      intro h; have : q = 1 := Complex.ofReal_injective h; dsimp [q] at this; linarith
    have hq_mem : (q : ℂ) ∈ t := by
      apply hball
      rw [Metric.mem_ball, Complex.dist_eq]
      have : (q : ℂ) - 1 = ((ε / 2 : ℝ) : ℂ) := by dsimp [q]; push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    exact ⟨(q : ℂ), hts ⟨hq_mem, hq_ne⟩, hreal_eq q hq_pos⟩
  have heqV : Set.EqOn F G V :=
    (hF_diff.analyticOnNhd hVopen).eqOn_of_preconnected_of_frequently_eq
      (hG_diff.analyticOnNhd hVopen) hVconn (by change -α' < (1 : ℂ).re; simp; linarith) hfreq
  have hz_mem : (-Complex.I * (ξ : ℂ)) ∈ V := by
    change -α' < (-Complex.I * (ξ : ℂ)).re
    simp; linarith
  have hval := heqV hz_mem
  have hG_val : G (-Complex.I * (ξ : ℂ)) = (β : ℂ) * Complex.log (1 - Complex.I * (((ξ / α' : ℝ) : ℂ))) := by
    dsimp [G]
    congr 2
    push_cast; ring
  rw [hG_val] at hval
  -- Convert ∫ x in Ioi 0, ... ∂(gammaLevyMeasure α' β) to -F (-I * ξ)
  unfold gammaLevyMeasure
  rw [restrict_withDensity measurableSet_Ioi,
    integral_withDensity_eq_integral_toReal_smul (measurable_gammaLevyDensity α' β)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hrew_int : ∫ x in Set.Ioi (0 : ℝ),
      (gammaLevyDensity α' β x).toReal • (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) =
      -F (-Complex.I * (ξ : ℂ)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hxpos : 0 < x := hx
    simp only [gammaLevyDensity, if_pos hxpos,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ β * x⁻¹ * Real.exp (-α' * x)),
      Complex.real_smul]
    have hexp : Complex.exp (-(-Complex.I * (ξ : ℂ)) * (x : ℂ)) =
        Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) := by
      congr 1; push_cast; ring
    rw [hexp]; ring
  rw [hrew_int, hval]; ring

private lemma gammaMeasure_laplace (a r q : ℝ) (ha : 0 < a) (hr : 0 < r) (hq : 0 ≤ q) :
    ∫ x, Real.exp (-q * x) ∂(ProbabilityTheory.gammaMeasure a r) =
      Real.exp (-a * Real.log (1 + q / r)) := by
  unfold ProbabilityTheory.gammaMeasure
  have hpdf_meas : Measurable (ProbabilityTheory.gammaPDF a r) :=
    ENNReal.measurable_ofReal.comp (ProbabilityTheory.measurable_gammaPDFReal a r)
  rw [integral_withDensity_eq_integral_toReal_smul hpdf_meas
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hrew : (fun x : ℝ => (ProbabilityTheory.gammaPDF a r x).toReal • Real.exp (-q * x)) =
      fun x : ℝ => (r / (r + q)) ^ a * ProbabilityTheory.gammaPDFReal a (r + q) x := by
    funext x
    simp only [ProbabilityTheory.gammaPDF, smul_eq_mul]
    unfold ProbabilityTheory.gammaPDFReal
    split_ifs with hx
    · have hnn : 0 ≤ r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) := by
        have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
        have hrpow : 0 ≤ r ^ a := Real.rpow_nonneg hr.le a
        have hxpow : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg hx (a - 1)
        positivity
      rw [ENNReal.toReal_ofReal hnn, Real.div_rpow hr.le (by linarith)]
      have hexp : Real.exp (-(r * x)) * Real.exp (-q * x) = Real.exp (-((r + q) * x)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hrq_ne : (r + q) ^ a ≠ 0 := (Real.rpow_pos_of_pos (by linarith) a).ne'
      calc r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) * Real.exp (-q * x)
          = r ^ a / Real.Gamma a * x ^ (a - 1) * (Real.exp (-(r * x)) * Real.exp (-q * x)) := by ring
        _ = r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-((r + q) * x)) := by rw [hexp]
        _ = r ^ a / (r + q) ^ a * ((r + q) ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-((r + q) * x))) := by
            field_simp [hrq_ne]
    · simp
  rw [hrew, integral_const_mul]
  have hprob : IsProbabilityMeasure (ProbabilityTheory.gammaMeasure a (r + q)) :=
    ProbabilityTheory.isProbabilityMeasure_gammaMeasure ha (by linarith)
  have hint1 : ∫ x, ProbabilityTheory.gammaPDFReal a (r + q) x = 1 := by
    have hpdf_meas2 : Measurable (ProbabilityTheory.gammaPDF a (r + q)) :=
      ENNReal.measurable_ofReal.comp (ProbabilityTheory.measurable_gammaPDFReal a (r + q))
    have h1 := integral_withDensity_eq_integral_toReal_smul (μ := volume) hpdf_meas2
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (fun _ : ℝ => (1 : ℝ))
    have huniv : ∫ _ : ℝ, (1 : ℝ) ∂(ProbabilityTheory.gammaMeasure a (r + q)) = 1 := by
      simp
    rw [← huniv]
    change ∫ x, ProbabilityTheory.gammaPDFReal a (r + q) x =
      ∫ _, (1 : ℝ) ∂(volume.withDensity (ProbabilityTheory.gammaPDF a (r + q)))
    rw [h1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ProbabilityTheory.gammaPDF, smul_eq_mul, mul_one]
    have hnn : 0 ≤ ProbabilityTheory.gammaPDFReal a (r + q) x :=
      ProbabilityTheory.gammaPDFReal_nonneg ha (by linarith) x
    exact (ENNReal.toReal_ofReal hnn).symm
  rw [hint1, mul_one, Real.rpow_def_of_pos (div_pos hr (by linarith))]
  congr 1
  have hinv : r / (r + q) = (1 + q / r)⁻¹ := by
    have : 1 + q / r = (r + q) / r := by field_simp [hr.ne']
    rw [this, inv_div]
  rw [hinv, Real.log_inv]; ring

private lemma isCadlag_of_uniform_approx
    (f : ℕ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ)
    (hcad : ∀ k, ProbabilityTheory.IsCadlag (f k))
    (hunif : ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k ≥ K, ∀ t ≤ T, |f k t - g t| < ε) :
    ProbabilityTheory.IsCadlag g := by
  intro t
  constructor
  · -- Right-continuity at t
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨K, hK⟩ := hunif (t + 1) (ε / 3) (by linarith)
    have hrc := Metric.tendsto_nhds.mp (hcad K t).1 (ε / 3) (by linarith)
    have hmem : Set.Ico t (t + 1) ∈ nhdsWithin t (Set.Ici t) :=
      Ico_mem_nhdsGE (by exact lt_add_of_pos_right t zero_lt_one)
    filter_upwards [hrc, hmem] with s hs hst
    rw [Real.dist_eq] at hs ⊢
    have h1 := hK K le_rfl s hst.2.le
    have h2 := hK K le_rfl t (le_self_add)
    have htri : |g s - g t| ≤ |g s - f K s| + |f K s - f K t| + |f K t - g t| := by
      have : g s - g t = (g s - f K s) + (f K s - f K t) + (f K t - g t) := by ring
      rw [this]
      have a1 := abs_add_le ((g s - f K s) + (f K s - f K t)) (f K t - g t)
      have a2 := abs_add_le (g s - f K s) (f K s - f K t)
      linarith
    rw [abs_sub_comm (g s) (f K s)] at htri
    linarith
  · -- Left limit at t
    by_cases ht0 : t = 0
    · subst ht0
      refine ⟨0, ?_⟩
      have hemp : Set.Iio (0 : ℝ≥0) = ∅ := by ext x; simp
      rw [hemp, nhdsWithin_empty]
      exact tendsto_bot
    · have htpos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht0
      have hne : (nhdsWithin t (Set.Iio t)).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
        intro δ hδ
        let s : ℝ≥0 := ⟨max 0 ((t : ℝ) - δ / 2), le_max_left _ _⟩
        refine ⟨s, ?_, ?_⟩
        · change (s : ℝ) < (t : ℝ)
          dsimp [s]
          exact max_lt (NNReal.coe_pos.mpr htpos) (by linarith)
        · rw [NNReal.dist_eq]
          have hst : (s : ℝ) ≤ (t : ℝ) := max_le (NNReal.coe_nonneg t) (by linarith)
          rw [abs_of_nonneg (sub_nonneg.mpr hst)]
          have : (t : ℝ) - δ / 2 ≤ (s : ℝ) := le_max_right _ _
          linarith
      choose l hl using fun k => (hcad k t).2
      have hcauchy : CauchySeq l := by
        rw [Metric.cauchySeq_iff]
        intro ε hε
        obtain ⟨K, hK⟩ := hunif t (ε / 4) (by linarith)
        refine ⟨K, fun m hm n hn => ?_⟩
        rw [Real.dist_eq]
        have hclose_m := Metric.tendsto_nhds.mp (hl m) (ε / 4) (by linarith)
        have hclose_n := Metric.tendsto_nhds.mp (hl n) (ε / 4) (by linarith)
        have hmem : Set.Iio t ∈ nhdsWithin t (Set.Iio t) := self_mem_nhdsWithin
        obtain ⟨s, hsm, hsn, hst⟩ := (hclose_m.and (hclose_n.and hmem)).exists
        rw [Real.dist_eq] at hsm hsn
        have h1 := hK m hm s hst.le
        have h2 := hK n hn s hst.le
        have htri : |l m - l n| ≤ |l m - f m s| + |f m s - g s| + |g s - f n s| + |f n s - l n| := by
          have : l m - l n = (l m - f m s) + (f m s - g s) + (g s - f n s) + (f n s - l n) := by ring
          rw [this]
          have a1 := abs_add_le ((l m - f m s) + (f m s - g s) + (g s - f n s)) (f n s - l n)
          have a2 := abs_add_le ((l m - f m s) + (f m s - g s)) (g s - f n s)
          have a3 := abs_add_le (l m - f m s) (f m s - g s)
          linarith
        rw [abs_sub_comm (l m) (f m s), abs_sub_comm (g s) (f n s)] at htri
        linarith
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
      refine ⟨L, ?_⟩
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨K₁, hK₁⟩ := hunif t (ε / 3) (by linarith)
      obtain ⟨K₂, hK₂⟩ := (Metric.tendsto_nhds.mp hL (ε / 3) (by linarith)).exists_forall_of_atTop
      let K := max K₁ K₂
      have hclose := Metric.tendsto_nhds.mp (hl K) (ε / 3) (by linarith)
      have hmem : Set.Iio t ∈ nhdsWithin t (Set.Iio t) := self_mem_nhdsWithin
      filter_upwards [hclose, hmem] with s hs hst
      rw [Real.dist_eq] at hs ⊢
      have h1 := hK₁ K (le_max_left _ _) s hst.le
      have h2 : |l K - L| < ε / 3 := by simpa [Real.dist_eq] using hK₂ K (le_max_right _ _)
      have htri : |g s - L| ≤ |g s - f K s| + |f K s - l K| + |l K - L| := by
        have : g s - L = (g s - f K s) + (f K s - l K) + (l K - L) := by ring
        rw [this]
        have a1 := abs_add_le ((g s - f K s) + (f K s - l K)) (l K - L)
        have a2 := abs_add_le (g s - f K s) (f K s - l K)
        linarith
      rw [abs_sub_comm (g s) (f K s)] at htri
      linarith

private lemma exists_gamma_subordinator (α' β : ℝ) (hα' : 0 < α') (hβ : 0 < β) :
    ∃ (Ω₁ : Type) (measΩ₁ : MeasurableSpace Ω₁),
      letI : MeasurableSpace Ω₁ := measΩ₁
      ∃ (P₁ : Measure Ω₁) (probP₁ : IsProbabilityMeasure P₁),
        letI : IsProbabilityMeasure P₁ := probP₁
        ∃ (Γ₁ : ℝ≥0 → Ω₁ → ℝ≥0),
          (∀ t : ℝ≥0, Measurable (fun ω => (Γ₁ t ω : ℝ))) ∧
          ProbabilityTheory.IsLevyProcess (fun t ω => (Γ₁ t ω : ℝ)) P₁ ∧
          (∀ᵐ ω ∂P₁, Monotone (fun t => Γ₁ t ω)) ∧
          (∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
            ∫ ω, Real.exp (-q * (Γ₁ t ω : ℝ)) ∂P₁ =
              Real.exp (-(t : ℝ) * β * Real.log (1 + q / α'))) := by
  let ν : Measure ℝ := gammaLevyMeasure α' β
  have : SigmaFinite ν := sigmaFinite_gammaLevyMeasure α' β hα' hβ
  obtain ⟨Ω₁, measΩ₁, P₁, probP₁, ⟨N⟩⟩ := Kyprianou.poissonRandomMeasureExists ν
  let _ : MeasurableSpace Ω₁ := measΩ₁
  have : IsProbabilityMeasure P₁ := probP₁
  let Γenn : ℝ≥0 → Ω₁ → ℝ≥0∞ := fun t ω =>
    ∫⁻ z in Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ), ENNReal.ofReal z.2 ∂(N.N ω)
  let Γ₁ : ℝ≥0 → Ω₁ → ℝ≥0 := fun t ω => (Γenn t ω).toNNReal
  -- Measurability of Γenn and Γ₁
  have hΓenn_meas : ∀ t : ℝ≥0, Measurable (Γenn t) := fun t => by
    have hset : MeasurableSet (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
      measurableSet_Ioc.prod measurableSet_Ioi
    have hfn : Measurable (Set.indicator (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ))
        (fun z : ℝ × ℝ => ENNReal.ofReal z.2)) :=
      (ENNReal.measurable_ofReal.comp measurable_snd).indicator hset
    have hrew : Γenn t = fun ω => ∫⁻ z,
        Set.indicator (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ))
          (fun z : ℝ × ℝ => ENNReal.ofReal z.2) z ∂(N.N ω) := by
      funext ω; exact (lintegral_indicator hset _).symm
    rw [hrew]
    exact (prm_campbell_lintegral P₁ ν N _ hfn).1
  have hΓ₁_meas : ∀ t : ℝ≥0, Measurable (fun ω => (Γ₁ t ω : ℝ)) := fun t => by
    have hrew : (fun ω => (Γ₁ t ω : ℝ)) = fun ω => (Γenn t ω).toReal := rfl
    rw [hrew]
    exact ENNReal.measurable_toReal.comp (hΓenn_meas t)
  -- Expected value of Γenn t is finite: t * β / α'
  have hΓenn_lintegral : ∀ t : ℝ≥0, ∫⁻ ω, Γenn t ω ∂P₁ = ENNReal.ofReal ((t : ℝ) * (β / α')) := by
    intro t
    have hset : MeasurableSet (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
      measurableSet_Ioc.prod measurableSet_Ioi
    have hfn : Measurable (Set.indicator (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ))
        (fun z : ℝ × ℝ => ENNReal.ofReal z.2)) :=
      (ENNReal.measurable_ofReal.comp measurable_snd).indicator hset
    have hrew : Γenn t = fun ω => ∫⁻ z,
        Set.indicator (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ))
          (fun z : ℝ × ℝ => ENNReal.ofReal z.2) z ∂(N.N ω) := by
      funext ω; exact (lintegral_indicator hset _).symm
    rw [hrew, (prm_campbell_lintegral P₁ ν N _ hfn).2, lintegral_indicator hset]
    unfold LevyStochCalc.Poisson.referenceIntensity
    rw [← Measure.prod_restrict,
      lintegral_prod (f := fun z : ℝ × ℝ => ENNReal.ofReal z.2)
        (ENNReal.measurable_ofReal.comp measurable_snd).aemeasurable]
    simp_rw [lintegral_const]
    have hIoc : (volume.restrict (Set.Ici (0 : ℝ))) (Set.Ioc (0 : ℝ) (t : ℝ)) = ENNReal.ofReal (t : ℝ) := by
      rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.mpr (fun x hx => hx.1.le),
        Real.volume_Ioc, sub_zero]
    rw [Measure.restrict_apply_univ, hIoc, gammaLevyMeasure_first_moment α' β hα' hβ,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  -- Almost surely Γenn t ω < ⊤ for all t : ℝ≥0 simultaneously
  have hΓenn_mono : ∀ ω, Monotone (fun t => Γenn t ω) := fun ω s t hst =>
    lintegral_mono_set (Set.prod_mono (Set.Ioc_subset_Ioc_right (NNReal.coe_le_coe.mpr hst)) Set.Subset.rfl)
  have hΓenn_fin_all : ∀ᵐ ω ∂P₁, ∀ t : ℝ≥0, Γenn t ω < ⊤ := by
    have hnat : ∀ n : ℕ, ∀ᵐ ω ∂P₁, Γenn (n : ℝ≥0) ω < ⊤ := fun n => by
      refine ae_lt_top (hΓenn_meas (n : ℝ≥0)) ?_
      rw [hΓenn_lintegral (n : ℝ≥0)]
      exact ENNReal.ofReal_ne_top
    rw [← ae_all_iff] at hnat
    filter_upwards [hnat] with ω hω t
    obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
    have hle : t ≤ (n : ℝ≥0) := by exact_mod_cast hn
    exact lt_of_le_of_lt (hΓenn_mono ω hle) (hω n)
  have hΓ₁_mono : ∀ᵐ ω ∂P₁, Monotone (fun t => Γ₁ t ω) := by
    filter_upwards [hΓenn_fin_all] with ω hω s t hst
    exact ENNReal.toNNReal_mono (hω t).ne (hΓenn_mono ω hst)
  -- Truncated compound Poisson processes Y k on B k = (1 / (k + 1), ∞)
  let B : ℕ → Set ℝ := fun k => Set.Ioi (1 / ((k : ℝ) + 1))
  have hB_meas : ∀ k, MeasurableSet (B k) := fun _ => measurableSet_Ioi
  have hB_fin : ∀ k, ν (B k) < ⊤ := fun k =>
    gammaLevyMeasure_Ioi_lt_top α' β (1 / ((k : ℝ) + 1)) hα' hβ (by positivity)
  let Y : ℕ → ℝ≥0 → Ω₁ → ℝ := fun k t ω =>
    ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B k), z.2 ∂(N.N ω)
  have hY_levy : ∀ k, ProbabilityTheory.IsLevyProcess (Y k) P₁ := fun k =>
    (Kyprianou.finiteRegionPoissonIntegralCh02V3 P₁ ν N (B k) (hB_meas k) (hB_fin k)).1
  have hY_char : ∀ k (t : ℝ≥0) (ξ : ℝ),
      charFun (P₁.map (Y k t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in B k, (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) := fun k =>
    (Kyprianou.finiteRegionPoissonIntegralCh02V3 P₁ ν N (B k) (hB_meas k) (hB_fin k)).2
  -- On {ω | ∀ t, Γenn t ω < ⊤}, Y k t ω converges monotonically and uniformly on [0, T] to Γ₁ t ω
  have hY_eq_toReal : ∀ ω, (∀ t : ℝ≥0, Γenn t ω < ⊤) → ∀ k (t : ℝ≥0),
      Y k t ω = (∫⁻ z in Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B k, ENNReal.ofReal z.2 ∂(N.N ω)).toReal := by
    intro ω hfin k t
    have hsub : Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B k ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.Ioi (0 : ℝ) :=
      Set.prod_mono Set.Subset.rfl (Set.Ioi_subset_Ioi (by positivity))
    have hnn : ∀ᵐ z ∂((N.N ω).restrict (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B k)), 0 ≤ z.2 := by
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod (hB_meas k))] with z hz
      exact le_trans (by positivity) hz.2.le
    have hint : IntegrableOn (fun z : ℝ × ℝ => z.2) (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B k) (N.N ω) := by
      refine ⟨measurable_snd.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral]
      have hcongr : ∫⁻ z in Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B k, ‖z.2‖ₑ ∂(N.N ω) =
          ∫⁻ z in Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B k, ENNReal.ofReal z.2 ∂(N.N ω) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hnn] with z hz
        rw [Real.enorm_eq_ofReal hz]
      rw [hcongr]
      exact lt_of_le_of_lt (lintegral_mono_set hsub) (hfin t)
    dsimp [Y]
    rw [integral_eq_lintegral_of_nonneg_ae hnn measurable_snd.aestronglyMeasurable]
  have hY_unif : ∀ ω, (∀ t : ℝ≥0, Γenn t ω < ⊤) →
      ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k ≥ K, ∀ t ≤ T, |Y k t ω - (Γ₁ t ω : ℝ)| < ε := by
    intro ω hfin T ε hε
    have hUnion : (⋃ k : ℕ, Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B k) = Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
      ext ⟨s, x⟩
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_Ioi, B]
      constructor
      · rintro ⟨k, hs, hx⟩; exact ⟨hs, lt_trans (by positivity) hx⟩
      · rintro ⟨hs, hx⟩
        obtain ⟨k, hk⟩ := exists_nat_gt (1 / x)
        refine ⟨k, hs, ?_⟩
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
        rw [div_lt_iff₀ hx] at hk
        linarith
    have hmonoB : Monotone (fun k => Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B k) := fun a b hab =>
      Set.prod_mono Set.Subset.rfl (Set.Ioi_subset_Ioi (by
        have : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hab 1
        exact one_div_le_one_div_of_le (by positivity) this))
    have htend_enn : Tendsto (fun k => ∫⁻ z in Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B k, ENNReal.ofReal z.2 ∂(N.N ω))
        atTop (nhds (Γenn T ω)) := by
      have hsup : (⨆ k : ℕ, ∫⁻ z in Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B k, ENNReal.ofReal z.2 ∂(N.N ω)) =
          Γenn T ω := by
        dsimp [Γenn]
        rw [← hUnion]
        have h1 : ∀ k, ∫⁻ z in Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B k, ENNReal.ofReal z.2 ∂(N.N ω) =
            ∫⁻ z, Set.indicator (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B k) (fun z : ℝ × ℝ => ENNReal.ofReal z.2) z ∂(N.N ω) :=
          fun k => (lintegral_indicator (measurableSet_Ioc.prod (hB_meas k)) _).symm
        simp_rw [h1]
        rw [← lintegral_iSup]
        · rw [← lintegral_indicator (MeasurableSet.iUnion fun k => measurableSet_Ioc.prod (hB_meas k))]
          refine lintegral_congr fun z => ?_
          by_cases hz : z ∈ ⋃ k, Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B k
          · rw [Set.indicator_of_mem hz]
            obtain ⟨k₀, hk₀⟩ := Set.mem_iUnion.mp hz
            apply le_antisymm
            · exact iSup_le fun k => by by_cases h : z ∈ Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B k <;> simp [h]
            · exact le_iSup_of_le k₀ (by simp [hk₀])
          · rw [Set.indicator_of_notMem hz]
            have : ∀ k, z ∉ Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B k := fun k hk => hz (Set.mem_iUnion.mpr ⟨k, hk⟩)
            simp [this]
        · intro k
          exact (ENNReal.measurable_ofReal.comp measurable_snd).indicator (measurableSet_Ioc.prod (hB_meas k))
        · intro a b hab z
          exact Set.indicator_le_indicator_of_subset (hmonoB hab) (fun _ => zero_le) z
      rw [← hsup]
      exact tendsto_atTop_iSup fun a b hab => lintegral_mono_set (hmonoB hab)
    have htend_real : Tendsto (fun k => Y k T ω) atTop (nhds (Γ₁ T ω : ℝ)) := by
      have hrew : (fun k => Y k T ω) = fun k =>
          (∫⁻ z in Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B k, ENNReal.ofReal z.2 ∂(N.N ω)).toReal :=
        funext fun k => hY_eq_toReal ω hfin k T
      rw [hrew]
      exact (ENNReal.continuousAt_toReal (hfin T).ne).tendsto.comp htend_enn
    obtain ⟨K, hK⟩ := (Metric.tendsto_nhds.mp htend_real ε hε).exists_forall_of_atTop
    refine ⟨K, fun k hk t ht => ?_⟩
    have hsplit : ∀ s : ℝ≥0,
        (Γ₁ s ω : ℝ) - Y k s ω =
          (∫⁻ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.Ioc (0 : ℝ) (1 / ((k : ℝ) + 1)),
            ENNReal.ofReal z.2 ∂(N.N ω)).toReal := by
      intro s
      have hdisj : Disjoint (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B k)
          (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.Ioc (0 : ℝ) (1 / ((k : ℝ) + 1))) := by
        rw [Set.disjoint_left]
        rintro ⟨_, x⟩ h1 h2
        exact not_lt_of_ge h2.2.2 h1.2
      have hunion : (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B k) ∪
          (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.Ioc (0 : ℝ) (1 / ((k : ℝ) + 1))) =
          Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
        ext ⟨u, x⟩
        simp only [Set.mem_union, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioc, B]
        constructor
        · rintro (⟨hu, hx⟩ | ⟨hu, hx1, _⟩)
          · exact ⟨hu, lt_trans (by positivity) hx⟩
          · exact ⟨hu, hx1⟩
        · rintro ⟨hu, hx⟩
          rcases lt_or_ge (1 / ((k : ℝ) + 1)) x with hgt | hle
          · exact Or.inl ⟨hu, hgt⟩
          · exact Or.inr ⟨hu, hx, hle⟩
      have hadd : Γenn s ω =
          (∫⁻ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B k, ENNReal.ofReal z.2 ∂(N.N ω)) +
          (∫⁻ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.Ioc (0 : ℝ) (1 / ((k : ℝ) + 1)),
            ENNReal.ofReal z.2 ∂(N.N ω)) := by
        dsimp [Γenn]
        rw [← hunion, lintegral_union (measurableSet_Ioc.prod measurableSet_Ioc) hdisj]
      have hfin1 : (∫⁻ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B k, ENNReal.ofReal z.2 ∂(N.N ω)) ≠ ⊤ :=
        ne_top_of_le_ne_top (hfin s).ne (by rw [hadd]; exact le_self_add)
      have hfin2 : (∫⁻ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.Ioc (0 : ℝ) (1 / ((k : ℝ) + 1)),
          ENNReal.ofReal z.2 ∂(N.N ω)) ≠ ⊤ :=
        ne_top_of_le_ne_top (hfin s).ne (by rw [hadd]; exact le_add_self)
      have htoReal : (Γ₁ s ω : ℝ) = Y k s ω +
          (∫⁻ z in Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ Set.Ioc (0 : ℝ) (1 / ((k : ℝ) + 1)),
            ENNReal.ofReal z.2 ∂(N.N ω)).toReal := by
        rw [hY_eq_toReal ω hfin k s]
        change (Γenn s ω).toReal = _
        rw [hadd, ENNReal.toReal_add hfin1 hfin2]
      linarith
    have hdiff_nn : 0 ≤ (Γ₁ t ω : ℝ) - Y k t ω := by rw [hsplit t]; exact ENNReal.toReal_nonneg
    have hdiff_le : (Γ₁ t ω : ℝ) - Y k t ω ≤ (Γ₁ T ω : ℝ) - Y k T ω := by
      rw [hsplit t, hsplit T]
      have hfinT : (∫⁻ z in Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ Set.Ioc (0 : ℝ) (1 / ((k : ℝ) + 1)),
          ENNReal.ofReal z.2 ∂(N.N ω)) ≠ ⊤ :=
        ne_top_of_le_ne_top (hfin T).ne
          (lintegral_mono_set (Set.prod_mono Set.Subset.rfl (fun _ hx => hx.1)))
      exact ENNReal.toReal_mono hfinT
        (lintegral_mono_set (Set.prod_mono (Set.Ioc_subset_Ioc_right (NNReal.coe_le_coe.mpr ht)) Set.Subset.rfl))
    have hTclose : |Y k T ω - (Γ₁ T ω : ℝ)| < ε := by simpa [Real.dist_eq] using hK k hk
    have hTdiff_nn : 0 ≤ (Γ₁ T ω : ℝ) - Y k T ω := by rw [hsplit T]; exact ENNReal.toReal_nonneg
    rw [abs_sub_comm, abs_of_nonneg hdiff_nn]
    rw [abs_sub_comm, abs_of_nonneg hTdiff_nn] at hTclose
    linarith
  -- Càdlàg paths of Γ₁
  have hΓ₁_cadlag : ∀ᵐ ω ∂P₁, ProbabilityTheory.IsCadlag (fun t => (Γ₁ t ω : ℝ)) := by
    have hall : ∀ᵐ ω ∂P₁, ∀ k, ProbabilityTheory.IsCadlag (fun t => Y k t ω) :=
      ae_all_iff.mpr fun k => (hY_levy k).cadlag_ae
    filter_upwards [hΓenn_fin_all, hall] with ω hfin hcad
    exact isCadlag_of_uniform_approx (fun k t => Y k t ω) (fun t => (Γ₁ t ω : ℝ)) hcad
      (hY_unif ω hfin)
  -- Pointwise convergence of Y k t ω → Γ₁ t ω a.e.
  have hY_tendsto_ae : ∀ t : ℝ≥0, ∀ᵐ ω ∂P₁, Tendsto (fun k => Y k t ω) atTop (nhds (Γ₁ t ω : ℝ)) := by
    intro t
    filter_upwards [hΓenn_fin_all] with ω hfin
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨K, hK⟩ := hY_unif ω hfin t ε hε
    exact Filter.eventually_atTop.mpr ⟨K, fun k hk => by simpa [Real.dist_eq] using hK k hk t le_rfl⟩
  -- Joint characteristic function of increments of Γ₁
  have hjoint_char : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (_ht : Monotone t) (ξ : Fin n → ℝ),
      ∫ ω, Complex.exp (∑ j : Fin n, Complex.I * (ξ j : ℂ) *
          (((Γ₁ (t j.succ) ω : ℝ) - (Γ₁ (t j.castSucc) ω : ℝ) : ℝ) : ℂ)) ∂P₁ =
        ∏ j : Fin n, Complex.exp (-((((t j.succ - t j.castSucc : ℝ≥0) : ℝ) : ℂ)) * (β : ℂ) *
          Complex.log (1 - Complex.I * (((ξ j / α' : ℝ) : ℂ)))) := by
    intro n t ht ξ
    have hY_joint : ∀ k,
        ∫ ω, Complex.exp (∑ j : Fin n, Complex.I * (ξ j : ℂ) *
            ((Y k (t j.succ) ω - Y k (t j.castSucc) ω : ℝ) : ℂ)) ∂P₁ =
          ∏ j : Fin n, Complex.exp ((((t j.succ - t j.castSucc : ℝ≥0) : ℝ) : ℂ) *
            ∫ x in B k, (Complex.exp (Complex.I * (((ξ j * x : ℝ) : ℂ))) - 1) ∂ν) := by
      intro k
      let Z : Fin n → Ω₁ → ℂ := fun j ω =>
        Complex.exp (Complex.I * (ξ j : ℂ) * ((Y k (t j.succ) ω - Y k (t j.castSucc) ω : ℝ) : ℂ))
      have hrew : (fun ω => Complex.exp (∑ j : Fin n, Complex.I * (ξ j : ℂ) *
            ((Y k (t j.succ) ω - Y k (t j.castSucc) ω : ℝ) : ℂ))) = ∏ j : Fin n, Z j := by
        funext ω; simp [Z, Complex.exp_sum, Finset.prod_apply]
      have hZ_indep : iIndepFun Z P₁ :=
        ((hY_levy k).indep_increments n t ht).comp
          (fun j y => Complex.exp (Complex.I * (ξ j : ℂ) * (y : ℂ)))
          (fun j => (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable)
      have hZ_meas : ∀ j, AEStronglyMeasurable (Z j) P₁ := fun j =>
        ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable.comp_aemeasurable
          ((levy_aemeasurable (hY_levy k) (t j.succ)).sub (levy_aemeasurable (hY_levy k) (t j.castSucc)))).aestronglyMeasurable
      rw [hrew, hZ_indep.integral_prod_eq_prod_integral hZ_meas]
      refine Finset.prod_congr rfl fun j _ => ?_
      have htsub : t j.castSucc + (t j.succ - t j.castSucc) = t j.succ :=
        add_tsub_cancel_of_le (ht (Fin.castSucc_le_succ j))
      have hid := (hY_levy k).stationary_increments (t j.castSucc) (t j.succ - t j.castSucc)
      rw [htsub] at hid
      let φ : ℝ → ℂ := fun y => Complex.exp (Complex.I * (ξ j : ℂ) * (y : ℂ))
      have hφ_m : Measurable φ :=
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable
      have h2 : (fun ω => φ (Y k (t j.succ - t j.castSucc) ω)) =
          φ ∘ ProbabilityTheory.increment (Y k) 0 (t j.succ - t j.castSucc) := by
        funext ω
        have h0 : Y k 0 ω = 0 := congrFun (hY_levy k).start_zero ω
        simp [ProbabilityTheory.increment, h0]
      have hstat : ∫ ω, Z j ω ∂P₁ = ∫ ω, φ (Y k (t j.succ - t j.castSucc) ω) ∂P₁ := by
        rw [h2]; exact (hid.comp hφ_m).integral_eq
      rw [hstat]
      have hchar_eq : ∫ ω, φ (Y k (t j.succ - t j.castSucc) ω) ∂P₁ =
          charFun (P₁.map (Y k (t j.succ - t j.castSucc))) (ξ j) := by
        rw [charFun_apply_real, integral_map (levy_aemeasurable (hY_levy k) _)
          (f := fun y : ℝ => Complex.exp ((ξ j : ℂ) * (y : ℂ) * Complex.I))
          (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        dsimp [φ]; congr 1; ring
      rw [hchar_eq, hY_char k (t j.succ - t j.castSucc) (ξ j)]
    have hlhs_tendsto : Tendsto (fun k =>
        ∫ ω, Complex.exp (∑ j : Fin n, Complex.I * (ξ j : ℂ) *
            ((Y k (t j.succ) ω - Y k (t j.castSucc) ω : ℝ) : ℂ)) ∂P₁) atTop
        (nhds (∫ ω, Complex.exp (∑ j : Fin n, Complex.I * (ξ j : ℂ) *
            (((Γ₁ (t j.succ) ω : ℝ) - (Γ₁ (t j.castSucc) ω : ℝ) : ℝ) : ℂ)) ∂P₁)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
      · intro k
        have hm : AEMeasurable (fun ω => ∑ j : Fin n, Complex.I * (ξ j : ℂ) *
            ((Y k (t j.succ) ω - Y k (t j.castSucc) ω : ℝ) : ℂ)) P₁ :=
          Finset.aemeasurable_fun_sum (Finset.univ : Finset (Fin n)) fun (j : Fin n) _ =>
            (Complex.continuous_ofReal.measurable.comp_aemeasurable
              ((levy_aemeasurable (hY_levy k) (t j.succ)).sub (levy_aemeasurable (hY_levy k) (t j.castSucc)))).const_mul _
        exact (Complex.continuous_exp.measurable.comp_aemeasurable hm).aestronglyMeasurable
      · intro k
        refine Eventually.of_forall fun ω => ?_
        rw [Complex.norm_exp]
        have hre : (∑ j : Fin n, Complex.I * (ξ j : ℂ) *
            ((Y k (t j.succ) ω - Y k (t j.castSucc) ω : ℝ) : ℂ)).re = 0 := by
          rw [Complex.re_sum]
          exact Finset.sum_eq_zero fun j _ => by simp
        rw [hre, Real.exp_zero]
      · have hall_t : ∀ᵐ ω ∂P₁, ∀ j : Fin (n + 1), Tendsto (fun k => Y k (t j) ω) atTop (nhds (Γ₁ (t j) ω : ℝ)) :=
          ae_all_iff.mpr fun j => hY_tendsto_ae (t j)
        filter_upwards [hall_t] with ω hω
        refine (Complex.continuous_exp.tendsto _).comp (tendsto_finsetSum Finset.univ fun j _ => ?_)
        exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp
          ((hω j.succ).sub (hω j.castSucc)))
    have hrhs_tendsto : Tendsto (fun k =>
        ∏ j : Fin n, Complex.exp ((((t j.succ - t j.castSucc : ℝ≥0) : ℝ) : ℂ) *
          ∫ x in B k, (Complex.exp (Complex.I * (((ξ j * x : ℝ) : ℂ))) - 1) ∂ν)) atTop
        (nhds (∏ j : Fin n, Complex.exp (-((((t j.succ - t j.castSucc : ℝ≥0) : ℝ) : ℂ)) * (β : ℂ) *
          Complex.log (1 - Complex.I * (((ξ j / α' : ℝ) : ℂ)))))) := by
      refine tendsto_finsetProd Finset.univ fun j _ => ?_
      have hint_j : Tendsto (fun k => ∫ x in B k, (Complex.exp (Complex.I * (((ξ j * x : ℝ) : ℂ))) - 1) ∂ν)
          atTop (nhds (∫ x in Set.Ioi (0 : ℝ), (Complex.exp (Complex.I * (((ξ j * x : ℝ) : ℂ))) - 1) ∂ν)) := by
        have hrew_k : ∀ k, ∫ x in B k, (Complex.exp (Complex.I * (((ξ j * x : ℝ) : ℂ))) - 1) ∂ν =
            ∫ x in Set.Ioi (0 : ℝ),
              Set.indicator (B k) (fun x : ℝ => Complex.exp (Complex.I * (((ξ j * x : ℝ) : ℂ))) - 1) x ∂ν := by
          intro k
          rw [setIntegral_indicator (hB_meas k),
            Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by positivity))]
        simp_rw [hrew_k]
        have hdom_int : IntegrableOn (fun x : ℝ => |ξ j| * x) (Set.Ioi (0 : ℝ)) ν := by
          have hx_int : IntegrableOn (fun x : ℝ => x) (Set.Ioi (0 : ℝ)) ν := by
            refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
            rw [HasFiniteIntegral]
            have hcongr : ∫⁻ x in Set.Ioi (0 : ℝ), ‖x‖ₑ ∂ν = ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal x ∂ν := by
              refine lintegral_congr_ae ?_
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
              rw [Real.enorm_eq_ofReal hx.le]
            rw [hcongr, gammaLevyMeasure_first_moment α' β hα' hβ]
            exact ENNReal.ofReal_lt_top
          exact hx_int.const_mul |ξ j|
        refine tendsto_integral_of_dominated_convergence (fun x : ℝ => |ξ j| * x) ?_ hdom_int ?_ ?_
        · intro k
          exact ((Complex.continuous_exp.measurable.comp
            (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
              (measurable_const.mul measurable_id)))).sub measurable_const).indicator (hB_meas k)
            |>.aestronglyMeasurable
        · intro k
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hxpos : 0 < x := hx
          by_cases hmem : x ∈ B k
          · rw [Set.indicator_of_mem hmem]
            have hz : (-Complex.I * (((ξ j * x : ℝ) : ℂ))).re = 0 := by simp
            have hbd := norm_one_sub_cexp_le (z := -Complex.I * (((ξ j * x : ℝ) : ℂ))) hz.ge
            have hneg : ‖Complex.exp (Complex.I * (((ξ j * x : ℝ) : ℂ))) - 1‖ =
                ‖1 - Complex.exp (-(-Complex.I * (((ξ j * x : ℝ) : ℂ))))‖ := by
              rw [norm_sub_rev]; congr 3; ring
            rw [hneg]
            calc ‖1 - Complex.exp (-(-Complex.I * (((ξ j * x : ℝ) : ℂ))))‖
                ≤ ‖-Complex.I * (((ξ j * x : ℝ) : ℂ))‖ := hbd
              _ = |ξ j| * x := by
                  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
                    Real.norm_eq_abs, abs_mul, abs_of_pos hxpos]
          · rw [Set.indicator_of_notMem hmem, norm_zero]
            exact mul_nonneg (abs_nonneg _) hxpos.le
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hxpos : 0 < x := hx
          obtain ⟨K, hK⟩ := exists_nat_gt (1 / x)
          refine tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨K, fun k hk => ?_⟩)
          have hmem : x ∈ B k := by
            change 1 / ((k : ℝ) + 1) < x
            have h1 : 1 / x < (k : ℝ) + 1 := by
              have : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
              linarith
            rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
            rw [div_lt_iff₀ hxpos] at h1
            linarith
          exact (Set.indicator_of_mem hmem
            (fun y => Complex.exp (Complex.I * (((ξ j * y : ℝ) : ℂ))) - 1)).symm
      rw [frullani_complex α' β (ξ j) hα' hβ] at hint_j
      have hmul := (tendsto_const_nhds (x := ((((t j.succ - t j.castSucc : ℝ≥0) : ℝ) : ℂ)))).mul hint_j
      have hcexp := (Complex.continuous_exp.tendsto _).comp hmul
      have hlim : ((((t j.succ - t j.castSucc : ℝ≥0) : ℝ) : ℂ)) *
          (-(β : ℂ) * Complex.log (1 - Complex.I * (((ξ j / α' : ℝ) : ℂ)))) =
          -((((t j.succ - t j.castSucc : ℝ≥0) : ℝ) : ℂ)) * (β : ℂ) *
            Complex.log (1 - Complex.I * (((ξ j / α' : ℝ) : ℂ))) := by ring
      rw [hlim] at hcexp
      exact hcexp
    simp_rw [hY_joint] at hlhs_tendsto
    exact tendsto_nhds_unique hlhs_tendsto hrhs_tendsto
  -- CharFun of increments of Γ₁
  have hΓ₁_zero : (fun ω => (Γ₁ 0 ω : ℝ)) = fun _ => 0 := by
    funext ω
    change (Γenn 0 ω).toReal = 0
    simp [Γenn]
  have hΓ₁_inc_char : ∀ s₁ s₂ : ℝ≥0, s₁ ≤ s₂ → ∀ ξ : ℝ,
      charFun (P₁.map (ProbabilityTheory.increment (fun t ω => (Γ₁ t ω : ℝ)) s₁ s₂)) ξ =
        Complex.exp (-((((s₂ - s₁ : ℝ≥0) : ℝ) : ℂ)) * (β : ℂ) *
          Complex.log (1 - Complex.I * (((ξ / α' : ℝ) : ℂ)))) := by
    intro s₁ s₂ hle ξ
    let ts : Fin 2 → ℝ≥0 := ![s₁, s₂]
    have hts : Monotone ts := by
      intro a b hab; fin_cases a <;> fin_cases b <;> simp [ts, hle] at hab ⊢
    have hj := hjoint_char 1 ts hts ![ξ]
    have hinc_meas : Measurable (ProbabilityTheory.increment (fun t ω => (Γ₁ t ω : ℝ)) s₁ s₂) :=
      (hΓ₁_meas s₂).sub (hΓ₁_meas s₁)
    rw [charFun_apply_real, integral_map hinc_meas.aemeasurable
      (f := fun y : ℝ => Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I))
      (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable]
    have hlhs : ∫ ω, Complex.exp ((ξ : ℂ) * ((ProbabilityTheory.increment (fun t ω => (Γ₁ t ω : ℝ)) s₁ s₂ ω : ℝ) : ℂ) * Complex.I) ∂P₁ =
        ∫ ω, Complex.exp (∑ j : Fin 1, Complex.I * ((![ξ] j : ℝ) : ℂ) *
          (((Γ₁ (ts j.succ) ω : ℝ) - (Γ₁ (ts j.castSucc) ω : ℝ) : ℝ) : ℂ)) ∂P₁ := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp [ts, ProbabilityTheory.increment]
      congr 1; ring
    rw [hlhs, hj]
    simp [ts]
  have hΓ₁_levy : ProbabilityTheory.IsLevyProcess (fun t ω => (Γ₁ t ω : ℝ)) P₁ := by
    refine ⟨hΓ₁_zero, ?_, ?_, hΓ₁_cadlag⟩
    · intro n t ht
      refine iIndepFun_of_joint_charFun P₁
        (fun j => ProbabilityTheory.increment (fun s ω => (Γ₁ s ω : ℝ)) (t j.castSucc) (t j.succ))
        (fun j => ((hΓ₁_meas (t j.succ)).sub (hΓ₁_meas (t j.castSucc))).aemeasurable) ?_
      intro ξ
      simp only [ProbabilityTheory.increment]
      rw [hjoint_char n t ht ξ]
      refine Finset.prod_congr rfl fun j _ => ?_
      exact (hΓ₁_inc_char (t j.castSucc) (t j.succ) (ht (Fin.castSucc_le_succ j)) (ξ j)).symm
    · intro s h
      refine identDistrib_of_charFun P₁
        ((hΓ₁_meas (s + h)).sub (hΓ₁_meas s)).aemeasurable
        ((hΓ₁_meas h).sub (hΓ₁_meas 0)).aemeasurable ?_
      intro ξ
      rw [hΓ₁_inc_char s (s + h) le_self_add ξ, hΓ₁_inc_char 0 h zero_le ξ]
      simp
  -- Laplace transform of Γ₁ t by matching characteristic function with gammaMeasure (t * β) α'
  have hΓ₁_laplace : ∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
      ∫ ω, Real.exp (-q * (Γ₁ t ω : ℝ)) ∂P₁ =
        Real.exp (-(t : ℝ) * β * Real.log (1 + q / α')) := by
    intro q hq t
    by_cases ht0 : t = 0
    · subst ht0
      have h0 : ∀ ω, (Γ₁ 0 ω : ℝ) = 0 := fun ω => congrFun hΓ₁_zero ω
      simp [h0]
    · have htpos : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht0)
      have ha_pos : 0 < (t : ℝ) * β := mul_pos htpos hβ
      let μg : Measure ℝ := ProbabilityTheory.gammaMeasure ((t : ℝ) * β) α'
      have : IsProbabilityMeasure μg := ProbabilityTheory.isProbabilityMeasure_gammaMeasure ha_pos hα'
      have : IsProbabilityMeasure (P₁.map (fun ω => (Γ₁ t ω : ℝ))) :=
        Measure.isProbabilityMeasure_map (hΓ₁_meas t).aemeasurable
      have hμg_nn : ∀ᵐ x ∂μg, 0 ≤ x := by
        dsimp [μg, ProbabilityTheory.gammaMeasure]
        have hms : MeasurableSet {a : ℝ | ¬ 0 ≤ a} :=
          (measurableSet_le measurable_const measurable_id).compl
        rw [ae_iff, withDensity_apply _ hms]
        refine setLIntegral_eq_zero hms fun x hx => ?_
        have hnot : ¬ (0 ≤ x) := hx
        simp [ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal, hnot]
      have hchar_eq : charFun (P₁.map (fun ω => (Γ₁ t ω : ℝ))) = charFun μg := by
        funext ξ
        have h1 : charFun (P₁.map (fun ω => (Γ₁ t ω : ℝ))) ξ =
            Complex.exp (-(((t : ℝ) : ℂ)) * (β : ℂ) *
              Complex.log (1 - Complex.I * (((ξ / α' : ℝ) : ℂ)))) := by
          have hrew : (fun ω => (Γ₁ t ω : ℝ)) =
              ProbabilityTheory.increment (fun s ω => (Γ₁ s ω : ℝ)) 0 t := by
            funext ω
            have h0 : (Γ₁ 0 ω : ℝ) = 0 := congrFun hΓ₁_zero ω
            simp [ProbabilityTheory.increment, h0]
          rw [hrew, hΓ₁_inc_char 0 t zero_le ξ]
          simp
        have h2 : charFun μg ξ =
            Complex.exp (-(((t : ℝ) : ℂ)) * (β : ℂ) *
              Complex.log (1 - Complex.I * (((ξ / α' : ℝ) : ℂ)))) := by
          rw [charFun_apply_real]
          have hrew : (fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)) =
              fun x : ℝ => Complex.exp (-(-Complex.I * (ξ : ℂ)) * ((id x : ℝ) : ℂ)) := by
            funext x; simp only [id]; congr 1; ring
          rw [hrew, laplace_to_complex_exp μg id aemeasurable_id hμg_nn α' ((t : ℝ) * β) hα'
            (fun r hr => gammaMeasure_laplace ((t : ℝ) * β) α' r ha_pos hα' hr)
            (-Complex.I * (ξ : ℂ)) (by simp)]
          congr 1
          have harg : 1 + -Complex.I * (ξ : ℂ) / (α' : ℂ) =
              1 - Complex.I * (((ξ / α' : ℝ) : ℂ)) := by push_cast; ring
          rw [harg]; push_cast; ring
        rw [h1, h2]
      have hlaw_eq : P₁.map (fun ω => (Γ₁ t ω : ℝ)) = μg := Measure.ext_of_charFun hchar_eq
      have hint_eq : ∫ ω, Real.exp (-q * (Γ₁ t ω : ℝ)) ∂P₁ = ∫ x, Real.exp (-q * x) ∂μg := by
        rw [← hlaw_eq, integral_map (hΓ₁_meas t).aemeasurable
          (f := fun x : ℝ => Real.exp (-q * x))
          (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable]
      rw [hint_eq, gammaMeasure_laplace ((t : ℝ) * β) α' q ha_pos hα' hq]
      congr 1; ring
  exact ⟨Ω₁, measΩ₁, P₁, probP₁, Γ₁, hΓ₁_meas, hΓ₁_levy, hΓ₁_mono, hΓ₁_laplace⟩

/-! ### Section 6: Lifting Lévy processes to a product space -/

private lemma isLevyProcess_comp_measurePreserving
    {Ω' Ω₁ : Type} [MeasurableSpace Ω'] [MeasurableSpace Ω₁]
    {P' : Measure Ω'} {P₁ : Measure Ω₁}
    [IsProbabilityMeasure P'] [IsProbabilityMeasure P₁]
    {φ : Ω' → Ω₁} (hφ : MeasurePreserving φ P' P₁)
    {Y : ℝ≥0 → Ω₁ → ℝ} (hY_meas : ∀ t, Measurable (Y t))
    (hY_levy : ProbabilityTheory.IsLevyProcess Y P₁) :
    ProbabilityTheory.IsLevyProcess (fun t ω => Y t (φ ω)) P' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext ω
    exact congrFun hY_levy.start_zero (φ ω)
  · intro n t ht
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    have hsets_meas : ∀ i ∈ S, MeasurableSet
        (ProbabilityTheory.increment Y (t i.castSucc) (t i.succ) ⁻¹' sets i) :=
      fun i hi => ((hY_meas (t i.succ)).sub (hY_meas (t i.castSucc))) (hsets i hi)
    have hpre_i : ∀ i : Fin n,
        ProbabilityTheory.increment (fun s ω => Y s (φ ω)) (t i.castSucc) (t i.succ) ⁻¹' sets i =
          φ ⁻¹' (ProbabilityTheory.increment Y (t i.castSucc) (t i.succ) ⁻¹' sets i) := by
      intro i; rfl
    have hpre_inter :
        (⋂ i ∈ S, ProbabilityTheory.increment (fun s ω => Y s (φ ω)) (t i.castSucc) (t i.succ) ⁻¹' sets i) =
          φ ⁻¹' (⋂ i ∈ S, ProbabilityTheory.increment Y (t i.castSucc) (t i.succ) ⁻¹' sets i) := by
      simp_rw [hpre_i, Set.preimage_iInter]
    have hmeas_inter : MeasurableSet
        (⋂ i ∈ S, ProbabilityTheory.increment Y (t i.castSucc) (t i.succ) ⁻¹' sets i) :=
      Finset.measurableSet_biInter S hsets_meas
    rw [hpre_inter, hφ.measure_preimage hmeas_inter.nullMeasurableSet]
    have hind := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp
      (hY_levy.indep_increments n t ht)) S hsets
    rw [hind]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hpre_i i, hφ.measure_preimage (hsets_meas i hi).nullMeasurableSet]
  · intro s h
    have hstat := hY_levy.stationary_increments s h
    have hm1 : Measurable (ProbabilityTheory.increment Y s (s + h)) :=
      (hY_meas (s + h)).sub (hY_meas s)
    have hm2 : Measurable (ProbabilityTheory.increment Y 0 h) :=
      (hY_meas h).sub (hY_meas 0)
    refine ⟨(hm1.comp hφ.measurable).aemeasurable, (hm2.comp hφ.measurable).aemeasurable, ?_⟩
    change P'.map (ProbabilityTheory.increment Y s (s + h) ∘ φ) =
      P'.map (ProbabilityTheory.increment Y 0 h ∘ φ)
    rw [← Measure.map_map hm1 hφ.measurable, ← Measure.map_map hm2 hφ.measurable,
      hφ.map_eq, hstat.map_eq]
  · exact hφ.quasiMeasurePreserving.ae hY_levy.cadlag_ae

private lemma iIndepFun_fin2_prod
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {E : Type} [MeasurableSpace E]
    (f : Ω₁ → E) (g : Ω₂ → E) :
    ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω₁ × Ω₂) => if i = 0 then f ω.1 else g ω.2)
      (P₁.prod P₂) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _hsets
  have hm0 : (P₁.prod P₂) ((fun ω : Ω₁ × Ω₂ => f ω.1) ⁻¹' sets 0) = P₁ (f ⁻¹' sets 0) := by
    have hpre : (fun ω : Ω₁ × Ω₂ => f ω.1) ⁻¹' sets 0 = (f ⁻¹' sets 0) ×ˢ Set.univ := by
      ext ⟨x, y⟩; simp
    rw [hpre, Measure.prod_prod, measure_univ, mul_one]
  have hm1 : (P₁.prod P₂) ((fun ω : Ω₁ × Ω₂ => g ω.2) ⁻¹' sets 1) = P₂ (g ⁻¹' sets 1) := by
    have hpre : (fun ω : Ω₁ × Ω₂ => g ω.2) ⁻¹' sets 1 = Set.univ ×ˢ (g ⁻¹' sets 1) := by
      ext ⟨x, y⟩; simp
    rw [hpre, Measure.prod_prod, measure_univ, one_mul]
  have hS : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
    by_cases ha : (0 : Fin 2) ∈ S <;> by_cases hb : (1 : Fin 2) ∈ S
    · right; right; right
      ext i; fin_cases i <;> simp [ha, hb]
    · right; left
      ext i; fin_cases i <;> simp [ha, hb]
    · right; right; left
      ext i; fin_cases i <;> simp [ha, hb]
    · left
      ext i; fin_cases i <;> simp [ha, hb]
  rcases hS with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · have hpair : (⋂ i ∈ ({0, 1} : Finset (Fin 2)),
        (fun ω : Ω₁ × Ω₂ => if i = 0 then f ω.1 else g ω.2) ⁻¹' sets i) =
        (f ⁻¹' sets 0) ×ˢ (g ⁻¹' sets 1) := by
      ext ⟨x, y⟩
      simp
    rw [hpair, Measure.prod_prod, Finset.prod_pair (by decide : (0 : Fin 2) ≠ 1)]
    simp [hm0, hm1]

end Exercise29Helpers

open Exercise29Helpers in
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (α β c σ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hσ : 0 < σ)
    (Γ : ℝ≥0 → Ω → ℝ≥0)
    (hΓlevy : ProbabilityTheory.IsLevyProcess
      (fun t ω => (Γ t ω : ℝ)) P)
    (hΓsub : ∀ᵐ ω ∂P, Monotone (fun t => Γ t ω))
    (hΓlaplace : ∀ (q : ℝ), 0 ≤ q → ∀ (t : ℝ≥0),
      ∫ ω, Real.exp (-q * (Γ t ω : ℝ)) ∂P =
        Real.exp (-(t : ℝ) * β * Real.log (1 + q / α)))
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hind : ProbabilityTheory.iIndepFun
      (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
        if i = 0 then B.W (t : ℝ) ω else (Γ t ω : ℝ)) P) :
    let X : ℝ≥0 → Ω → ℝ := fun t ω =>
      c * (Γ t ω : ℝ) + σ * (B.W (Γ t ω : ℝ) ω - B.W 0 ω)
    let αpos : ℝ :=
      (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α))
        + c / (2 * α))⁻¹
    let αneg : ℝ :=
      (Real.sqrt (c ^ 2 / (4 * α ^ 2) + σ ^ 2 / (2 * α))
        - c / (2 * α))⁻¹
    (ProbabilityTheory.IsLevyProcess X P ∧
      ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P.map (X t)) ξ =
        Complex.exp (-(((t : ℝ) : ℂ)) * (β : ℂ) *
          Complex.log (1 - Complex.I *
            (((ξ * c / α : ℝ) : ℂ)) +
            (((σ ^ 2 * ξ ^ 2 / (2 * α) : ℝ) : ℂ)))) ∧
    (∃ (Ω' : Type) (measΩ' : MeasurableSpace Ω'),
      letI : MeasurableSpace Ω' := measΩ'
      ∃ (P' : Measure Ω') (probP' : IsProbabilityMeasure P'),
        letI : IsProbabilityMeasure P' := probP'
        ∃ (Γpos Γneg : ℝ≥0 → Ω' → ℝ≥0),
          ProbabilityTheory.IsLevyProcess
            (fun t ω => (Γpos t ω : ℝ)) P' ∧
          ProbabilityTheory.IsLevyProcess
            (fun t ω => (Γneg t ω : ℝ)) P' ∧
          (∀ᵐ ω ∂P', Monotone (fun t => Γpos t ω)) ∧
          (∀ᵐ ω ∂P', Monotone (fun t => Γneg t ω)) ∧
          ProbabilityTheory.iIndepFun
            (fun (i : Fin 2) (ω : Ω') => fun t : ℝ≥0 =>
              if i = 0 then (Γpos t ω : ℝ) else (Γneg t ω : ℝ)) P' ∧
          (∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
            ∫ ω, Real.exp (-q * (Γpos t ω : ℝ)) ∂P' =
              Real.exp (-(t : ℝ) * β *
                Real.log (1 + q / αpos))) ∧
          (∀ q : ℝ, 0 ≤ q → ∀ t : ℝ≥0,
            ∫ ω, Real.exp (-q * (Γneg t ω : ℝ)) ∂P' =
              Real.exp (-(t : ℝ) * β *
                Real.log (1 + q / αneg))) ∧
          (∀ t : ℝ≥0, ∀ ξ : ℝ,
            charFun (P.map (X t)) ξ =
            charFun (P'.map (fun ω =>
              (Γpos t ω : ℝ) - (Γneg t ω : ℝ))) ξ))) := by
  intro X αpos αneg
  have hX_levy : ProbabilityTheory.IsLevyProcess X P :=
    vg_isLevyProcess P α β c σ hα Γ hΓlevy hΓsub hΓlaplace B hind
  have hX_char : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
      Complex.exp (-(((t : ℝ) : ℂ)) * (β : ℂ) *
        Complex.log (1 - Complex.I * (((ξ * c / α : ℝ) : ℂ)) +
          (((σ ^ 2 * ξ ^ 2 / (2 * α) : ℝ) : ℂ)))) :=
    fun t ξ => vg_charFun P α β c σ hα Γ hΓlevy hΓsub hΓlaplace B hind t ξ
  have hαpos : 0 < αpos := alpha_pos_pos α c σ hα hσ
  have hαneg : 0 < αneg := alpha_neg_pos α c σ hα hσ
  obtain ⟨Ω₁, measΩ₁, P₁, probP₁, Γ₁, hΓ₁_meas, hΓ₁_levy, hΓ₁_mono, hΓ₁_lap⟩ :=
    exists_gamma_subordinator αpos β hαpos hβ
  obtain ⟨Ω₂, measΩ₂, P₂, probP₂, Γ₂, hΓ₂_meas, hΓ₂_levy, hΓ₂_mono, hΓ₂_lap⟩ :=
    exists_gamma_subordinator αneg β hαneg hβ
  let _ : MeasurableSpace Ω₁ := measΩ₁
  let _ : MeasurableSpace Ω₂ := measΩ₂
  have : IsProbabilityMeasure P₁ := probP₁
  have : IsProbabilityMeasure P₂ := probP₂
  let Ω' : Type := Ω₁ × Ω₂
  let measΩ' : MeasurableSpace Ω' := inferInstance
  let P' : Measure Ω' := P₁.prod P₂
  have probP' : IsProbabilityMeasure P' := inferInstance
  let Γpos : ℝ≥0 → Ω' → ℝ≥0 := fun t ω => Γ₁ t ω.1
  let Γneg : ℝ≥0 → Ω' → ℝ≥0 := fun t ω => Γ₂ t ω.2
  have hfst : MeasurePreserving (Prod.fst : Ω' → Ω₁) P' P₁ := measurePreserving_fst
  have hsnd : MeasurePreserving (Prod.snd : Ω' → Ω₂) P' P₂ := measurePreserving_snd
  refine ⟨hX_levy, fun t ξ => ⟨hX_char t ξ, ?_⟩⟩
  refine ⟨Ω', measΩ', P', probP', Γpos, Γneg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isLevyProcess_comp_measurePreserving hfst hΓ₁_meas hΓ₁_levy
  · exact isLevyProcess_comp_measurePreserving hsnd hΓ₂_meas hΓ₂_levy
  · exact hfst.quasiMeasurePreserving.ae hΓ₁_mono
  · exact hsnd.quasiMeasurePreserving.ae hΓ₂_mono
  · have hrew : (fun (i : Fin 2) (ω : Ω') => fun t : ℝ≥0 =>
        if i = 0 then (Γpos t ω : ℝ) else (Γneg t ω : ℝ)) =
        fun (i : Fin 2) (ω : Ω₁ × Ω₂) =>
          if i = 0 then (fun t : ℝ≥0 => (Γ₁ t ω.1 : ℝ)) else (fun t : ℝ≥0 => (Γ₂ t ω.2 : ℝ)) := by
      funext i ω t; split_ifs <;> rfl
    rw [hrew]
    exact iIndepFun_fin2_prod P₁ P₂
      (fun ω₁ t => (Γ₁ t ω₁ : ℝ)) (fun ω₂ t => (Γ₂ t ω₂ : ℝ))
  · intro q hq t
    have hmp : ∫ ω : Ω', Real.exp (-q * (Γ₁ t ω.1 : ℝ)) ∂P' =
        ∫ ω₁ : Ω₁, Real.exp (-q * (Γ₁ t ω₁ : ℝ)) ∂P₁ := by
      have h1 := MeasureTheory.integral_prod_mul (μ := P₁) (ν := P₂)
        (fun ω₁ : Ω₁ => Real.exp (-q * (Γ₁ t ω₁ : ℝ))) (fun _ : Ω₂ => (1 : ℝ))
      simpa using h1
    rw [hmp, hΓ₁_lap q hq t]
  · intro q hq t
    have hmp : ∫ ω : Ω', Real.exp (-q * (Γ₂ t ω.2 : ℝ)) ∂P' =
        ∫ ω₂ : Ω₂, Real.exp (-q * (Γ₂ t ω₂ : ℝ)) ∂P₂ := by
      have h1 := MeasureTheory.integral_prod_mul (μ := P₁) (ν := P₂)
        (fun _ : Ω₁ => (1 : ℝ)) (fun ω₂ : Ω₂ => Real.exp (-q * (Γ₂ t ω₂ : ℝ)))
      simpa using h1
    rw [hmp, hΓ₂_lap q hq t]
  · intro t ξ
    rw [hX_char t ξ]
    have hdiff_meas : Measurable (fun ω : Ω' => (Γpos t ω : ℝ) - (Γneg t ω : ℝ)) :=
      ((hΓ₁_meas t).comp measurable_fst).sub ((hΓ₂_meas t).comp measurable_snd)
    rw [charFun_apply_real, integral_map hdiff_meas.aemeasurable
      (f := fun y : ℝ => Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I))
      (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable]
    have hsplit : (fun ω : Ω' => Complex.exp ((ξ : ℂ) * (((Γpos t ω : ℝ) - (Γneg t ω : ℝ) : ℝ) : ℂ) * Complex.I)) =
        fun ω : Ω₁ × Ω₂ =>
          Complex.exp (-(-Complex.I * (ξ : ℂ)) * ((Γ₁ t ω.1 : ℝ) : ℂ)) *
          Complex.exp (-(Complex.I * (ξ : ℂ)) * ((Γ₂ t ω.2 : ℝ) : ℂ)) := by
      funext ⟨ω₁, ω₂⟩
      rw [← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hsplit]
    change _ = ∫ ω : Ω₁ × Ω₂,
        Complex.exp (-(-Complex.I * (ξ : ℂ)) * ((Γ₁ t ω.1 : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * (ξ : ℂ)) * ((Γ₂ t ω.2 : ℝ) : ℂ)) ∂(P₁.prod P₂)
    rw [MeasureTheory.integral_prod_mul (μ := P₁) (ν := P₂)
      (fun ω₁ : Ω₁ => Complex.exp (-(-Complex.I * (ξ : ℂ)) * ((Γ₁ t ω₁ : ℝ) : ℂ)))
      (fun ω₂ : Ω₂ => Complex.exp (-(Complex.I * (ξ : ℂ)) * ((Γ₂ t ω₂ : ℝ) : ℂ)))]
    have h1 := laplace_to_complex_exp P₁ (fun ω₁ => (Γ₁ t ω₁ : ℝ)) (hΓ₁_meas t).aemeasurable
      (Eventually.of_forall fun ω₁ => NNReal.coe_nonneg _) αpos ((t : ℝ) * β) hαpos
      (fun q hq => by
        rw [hΓ₁_lap q hq t]; congr 1; ring)
      (-Complex.I * (ξ : ℂ)) (by simp)
    have h2 := laplace_to_complex_exp P₂ (fun ω₂ => (Γ₂ t ω₂ : ℝ)) (hΓ₂_meas t).aemeasurable
      (Eventually.of_forall fun ω₂ => NNReal.coe_nonneg _) αneg ((t : ℝ) * β) hαneg
      (fun q hq => by
        rw [hΓ₂_lap q hq t]; congr 1; ring)
      (Complex.I * (ξ : ℂ)) (by simp)
    rw [h1, h2, ← Complex.exp_add]
    have hlog1 : 1 + -Complex.I * (ξ : ℂ) / (αpos : ℂ) = 1 - Complex.I * (((ξ / αpos : ℝ) : ℂ)) := by
      push_cast; ring
    have hlog2 : 1 + Complex.I * (ξ : ℂ) / (αneg : ℂ) = 1 + Complex.I * (((ξ / αneg : ℝ) : ℂ)) := by
      push_cast; ring
    rw [hlog1, hlog2]
    have hsum : -(((t : ℝ) * β : ℝ) : ℂ) * Complex.log (1 - Complex.I * (((ξ / αpos : ℝ) : ℂ))) +
        -(((t : ℝ) * β : ℝ) : ℂ) * Complex.log (1 + Complex.I * (((ξ / αneg : ℝ) : ℂ))) =
        -(((t : ℝ) : ℂ)) * (β : ℂ) *
          (Complex.log (1 - Complex.I * (((ξ / αpos : ℝ) : ℂ))) +
           Complex.log (1 + Complex.I * (((ξ / αneg : ℝ) : ℂ)))) := by
      push_cast; ring
    rw [hsum, vg_complex_log_add α c σ ξ hα hσ]
