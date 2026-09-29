-- Prove2me | solution 1 for LesHouchesWidth.gaussPairAvg_relu
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T06:30:07.742824+00:00
-- url     : https://prove2.me/submissions/47cb9e74-4bbe-42d1-a7d0-3babfd2f11c5

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP

/-! Supporting lemmas (Gaussian network layer calculus; checked). -/

set_option autoImplicit false

namespace LesHouchesWidth
namespace FW

open MeasureTheory ProbabilityTheory


/-- polynomially bounded measurable functions. -/
def PB (f : ℝ → ℝ) : Prop := Measurable f ∧ ∃ C : ℝ, ∃ k : ℕ, ∀ t, |f t| ≤ C * (1 + |t|) ^ k



section rowLaw

open Complex Matrix
open scoped RealInnerProductSpace

/-- characteristic integral of a linear form of iid standard Gaussians (from c38c8303). -/
lemma integral_cexp_linear {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    ∫ u : κ → ℝ, cexp ((∑ k, c k * u k : ℝ) * I) ∂(Measure.pi fun _ : κ => gaussianReal 0 1)
      = cexp (-(∑ k, c k ^ 2 : ℝ) / 2) := by
  have h := integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun k (x : ℝ) => cexp ((c k * x : ℝ) * I)) (μ := fun _ : κ => gaussianReal 0 1)
  have h2 : ∀ k, ∫ x, cexp ((c k * x : ℝ) * I) ∂gaussianReal 0 1 = cexp (-(c k ^ 2 : ℝ) / 2) := by
    intro k
    have := charFun_gaussianReal (μ := 0) (v := 1) (c k)
    rw [charFun_apply_real] at this
    push_cast at this ⊢
    rw [this]; congr 1; ring
  calc ∫ u : κ → ℝ, cexp ((∑ k, c k * u k : ℝ) * I) ∂(Measure.pi fun _ : κ => gaussianReal 0 1)
      = ∫ u : κ → ℝ, ∏ k, cexp ((c k * u k : ℝ) * I)
          ∂(Measure.pi fun _ : κ => gaussianReal 0 1) := by
        congr 1 with u
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        rw [Finset.sum_mul]
    _ = ∏ k, cexp (-(c k ^ 2 : ℝ) / 2) := by rw [h]; simp only [h2]
    _ = cexp (-(∑ k, c k ^ 2 : ℝ) / 2) := by
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        simp only [neg_div, Finset.sum_neg_distrib, Finset.sum_div]

lemma map_pi_gaussian_linear {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℝ) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun u => WithLp.toLp 2 (A *ᵥ u)) =
      multivariateGaussian 0 (A * A.transpose) := by
  have hPSD : (A * A.transpose).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hmeas : Measurable (fun u : κ → ℝ => WithLp.toLp 2 (A *ᵥ u)) :=
    ((PiLp.continuous_toLp 2 _).comp (Continuous.matrix_mulVec continuous_const continuous_id)).measurable
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_multivariateGaussian hPSD, charFun_apply,
    integral_map hmeas.aemeasurable (by fun_prop)]
  have hinner : ∀ u : κ → ℝ,
      ⟪WithLp.toLp 2 (A *ᵥ u), s⟫ = ∑ k, (A.transpose *ᵥ s.ofLp) k * u k := by
    intro u
    simp only [PiLp.inner_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      RCLike.inner_apply, conj_trivial, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [hinner]
  rw [integral_cexp_linear]
  have hq : ∑ k, (A.transpose *ᵥ s.ofLp) k ^ 2 = s.ofLp ⬝ᵥ (A * A.transpose) *ᵥ s.ofLp := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp [dotProduct, sq]
  rw [hq]
  congr 1
  simp [neg_div]

lemma map_pi_gaussian_linear_eval {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (i : ι) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun u => (A *ᵥ u) i) =
      gaussianReal 0 ((A * A.transpose) i i).toNNReal := by
  have hPSD : (A * A.transpose).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hmeas : Measurable (fun u : κ → ℝ => WithLp.toLp 2 (A *ᵥ u)) :=
    ((PiLp.continuous_toLp 2 _).comp (Continuous.matrix_mulVec continuous_const continuous_id)).measurable
  rw [show (fun u => (A *ᵥ u) i) =
      (fun v : EuclideanSpace ℝ ι => v i) ∘ (fun u => WithLp.toLp 2 (A *ᵥ u)) from rfl,
    ← Measure.map_map (PiLp.continuous_apply 2 _ i).measurable hmeas, map_pi_gaussian_linear,
    (measurePreserving_eval_multivariateGaussian hPSD).map_eq]
  simp

/-- law of a linear form of iid standard Gaussians. -/
lemma rowLaw {κ : Type*} [Fintype κ] (c : κ → ℝ) :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun u => ∑ q, c q * u q) =
      gaussianReal 0 (∑ q, c q ^ 2).toNNReal := by
  have h := map_pi_gaussian_linear_eval (ι := Fin 1) (Matrix.of fun (_ : Fin 1) q => c q) 0
  have e1 : (fun u : κ → ℝ => ((Matrix.of fun (_ : Fin 1) q => c q) *ᵥ u) 0) =
      fun u => ∑ q, c q * u q := by
    funext u; simp [Matrix.mulVec, dotProduct]
  have e2 : ((Matrix.of fun (_ : Fin 1) q => c q) *
      (Matrix.of fun (_ : Fin 1) q => c q).transpose) 0 0 = ∑ q, c q ^ 2 := by
    simp [Matrix.mul_apply, sq]
  rw [e1, e2] at h
  exact h

/-- joint law of independent rows. -/
lemma rowsLaw {ι κ : Type*} [Fintype ι] [Fintype κ] (c : κ → ℝ) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1).map
      (fun Y i => ∑ q, c q * Y i q) =
      Measure.pi fun _ : ι => gaussianReal 0 (∑ q, c q ^ 2).toNNReal := by
  rw [Measure.pi_map_pi (f := fun _ (u : κ → ℝ) => ∑ q, c q * u q)
    (fun _ => (Finset.measurable_sum _ fun q _ => by fun_prop).aemeasurable)]
  simp only [rowLaw]

end rowLaw









end FW
end LesHouchesWidth


set_option autoImplicit false

namespace LesHouchesWidth
namespace FW

open MeasureTheory ProbabilityTheory Real

section reluPair

lemma max_mul_of_nonneg {c t : ℝ} (hc : 0 ≤ c) : max (c * t) 0 = c * max t 0 := by
  rcases le_total t 0 with h | h
  · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc h), mul_zero]
  · rw [max_eq_left h, max_eq_left (mul_nonneg hc h)]

/-- the angular integral of the ReLU pair kernel. -/
lemma angular {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    ∫ φ in Set.Ioo (-π) π, max (cos φ) 0 * max (cos (φ - θ)) 0 =
      (sin θ + (π - θ) * cos θ) / 2 := by
  have hpi := Real.pi_pos
  have hc : Continuous (fun φ : ℝ => max (cos φ) 0 * max (cos (φ - θ)) 0) :=
    (continuous_cos.max continuous_const).mul
      ((continuous_cos.comp (continuous_id.sub continuous_const)).max continuous_const)
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun φ : ℝ => max (cos φ) 0 * max (cos (φ - θ)) 0)
      volume a b := fun a b => hc.intervalIntegrable a b
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (hii (-π) (θ - π / 2)) (hii (θ - π / 2) π),
    ← intervalIntegral.integral_add_adjacent_intervals (hii (θ - π / 2) (π / 2)) (hii (π / 2) π)]
  have z1 : ∫ φ in (-π)..(θ - π / 2), max (cos φ) 0 * max (cos (φ - θ)) 0 = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
    · simp
    intro φ hφ
    rw [Set.uIcc_of_le (by linarith)] at hφ
    obtain ⟨h1, h2⟩ := hφ
    rcases le_total φ (-(π / 2)) with h3 | h3
    · have : cos φ ≤ 0 := by
        rw [← cos_neg]; exact cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      simp only [max_eq_right this, zero_mul]
    · have : cos (φ - θ) ≤ 0 := by
        rw [← cos_neg]; exact cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
      simp only [max_eq_right this, mul_zero]
  have z3 : ∫ φ in (π / 2)..π, max (cos φ) 0 * max (cos (φ - θ)) 0 = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
    · simp
    intro φ hφ
    rw [Set.uIcc_of_le (by linarith)] at hφ
    obtain ⟨h1, h2⟩ := hφ
    have : cos φ ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith)
    simp only [max_eq_right this, zero_mul]
  have hd : ∀ φ : ℝ, HasDerivAt (fun φ : ℝ => sin (2 * φ - θ) / 4 + φ * cos θ / 2)
      (cos φ * cos (φ - θ)) φ := by
    intro φ
    have h1 : HasDerivAt (fun φ : ℝ => 2 * φ - θ) 2 φ := by
      simpa using ((hasDerivAt_id' φ).const_mul 2).sub_const θ
    have h2 := (h1.sin.div_const 4).add (((hasDerivAt_id' φ).mul_const (cos θ)).div_const 2)
    refine h2.congr_deriv ?_
    have e1 : cos (2 * φ - θ) = cos φ * cos (φ - θ) - sin φ * sin (φ - θ) := by
      rw [show 2 * φ - θ = φ + (φ - θ) by ring, cos_add]
    have e2 : cos θ = cos φ * cos (φ - θ) + sin φ * sin (φ - θ) := by
      rw [← cos_sub, show φ - (φ - θ) = θ by ring]
    rw [e1, e2]
    ring
  have m2 : ∫ φ in (θ - π / 2)..(π / 2), max (cos φ) 0 * max (cos (φ - θ)) 0 =
      (sin θ + (π - θ) * cos θ) / 2 := by
    rw [intervalIntegral.integral_congr (g := fun φ => cos φ * cos (φ - θ)) ?_]
    · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun φ _ => hd φ)
        ((continuous_cos.mul (continuous_cos.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _)]
      rw [show 2 * (π / 2) - θ = π - θ by ring, show 2 * (θ - π / 2) - θ = θ - π by ring,
        sin_pi_sub, sin_sub_pi]
      ring
    intro φ hφ
    rw [Set.uIcc_of_le (by linarith)] at hφ
    obtain ⟨h1, h2⟩ := hφ
    have c1 : 0 ≤ cos φ := cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
    have c2 : 0 ≤ cos (φ - θ) := cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) (by linarith)
    simp only [max_eq_left c1, max_eq_left c2]
  rw [z1, z3, m2]
  ring

/-- the radial integral `∫₀^∞ r³ e^{-r²/2} dr = 2`. -/
lemma radial : ∫ r in Set.Ioi (0:ℝ), r ^ 3 * rexp (-(1 / 2) * r ^ 2) = 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have e1 : ∀ r : ℝ, r ^ (3 : ℝ) * rexp (-(1 / 2) * r ^ (2 : ℝ)) = r ^ 3 * rexp (-(1 / 2) * r ^ 2) := by
    intro r
    rw [Real.rpow_ofNat, Real.rpow_ofNat]
  simp only [e1] at h
  rw [h, show (-((3:ℝ) + 1) / 2) = -2 by norm_num, show ((3:ℝ) + 1) / 2 = 2 by norm_num,
    Real.Gamma_two, Real.rpow_neg (by norm_num), Real.rpow_two]
  norm_num

/-- `E[relu(g₀) relu(cos θ g₀ + sin θ g₁)]` for a standard Gaussian pair. -/
lemma J_eq {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    ∫ g, max (g 0) 0 * max (cos θ * g 0 + sin θ * g 1) 0
      ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) = (sin θ + (π - θ) * cos θ) / (2 * π) := by
  have hpi := Real.pi_pos
  have hmp := measurePreserving_finTwoArrow (gaussianReal 0 1)
  have h1 := hmp.integral_comp' (fun p : ℝ × ℝ => max p.1 0 * max (cos θ * p.1 + sin θ * p.2) 0)
  have e1 : (∫ g, max (g 0) 0 * max (cos θ * g 0 + sin θ * g 1) 0
      ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1)) =
      ∫ g, (fun p : ℝ × ℝ => max p.1 0 * max (cos θ * p.1 + sin θ * p.2) 0)
        (MeasurableEquiv.finTwoArrow g) ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := rfl
  rw [e1, h1, gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity₀ (measurable_gaussianPDF 0 1).aemeasurable
      (measurable_gaussianPDF 0 1).aemeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun z : ℝ × ℝ => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) from
        ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
          ((measurable_gaussianPDF 0 1).comp measurable_snd))
      (Filter.Eventually.of_forall fun z => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top),
    ← Measure.volume_eq_prod, ← integral_comp_polarCoord_symm]
  have hts : polarCoord.target = Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π := rfl
  rw [hts]
  have hEq : Set.EqOn (fun p : ℝ × ℝ => p.1 • ((gaussianPDF 0 1 (polarCoord.symm p).1 *
        gaussianPDF 0 1 (polarCoord.symm p).2).toReal • (fun q : ℝ × ℝ => max q.1 0 *
          max (cos θ * q.1 + sin θ * q.2) 0) (polarCoord.symm p)))
      (fun p : ℝ × ℝ => ((2 * π)⁻¹ * (p.1 ^ 3 * rexp (-(1 / 2) * p.1 ^ 2))) *
        (max (cos p.2) 0 * max (cos (p.2 - θ)) 0))
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π) := by
    rintro ⟨r, φ⟩ ⟨hr, _⟩
    simp only [Set.mem_Ioi] at hr
    simp only [polarCoord_symm_apply, smul_eq_mul]
    rw [ENNReal.toReal_mul]
    simp only [gaussianPDF]
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
      ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    simp only [gaussianPDFReal_def, NNReal.coe_one, sub_zero, mul_one]
    have ea : cos θ * (r * cos φ) + sin θ * (r * sin φ) = r * cos (φ - θ) := by
      rw [cos_sub]; ring
    rw [ea, max_mul_of_nonneg hr.le, max_mul_of_nonneg hr.le]
    have eb : rexp (-(r * cos φ) ^ 2 / 2) * rexp (-(r * sin φ) ^ 2 / 2) =
        rexp (-(1 / 2) * r ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      have := sin_sq_add_cos_sq φ
      linear_combination (-(r ^ 2) / 2) * this
    have ec : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    calc r * ((√(2 * π))⁻¹ * rexp (-(r * cos φ) ^ 2 / 2) *
          ((√(2 * π))⁻¹ * rexp (-(r * sin φ) ^ 2 / 2)) *
          (r * max (cos φ) 0 * (r * max (cos (φ - θ)) 0)))
        = ((√(2 * π))⁻¹ * (√(2 * π))⁻¹) * (rexp (-(r * cos φ) ^ 2 / 2) *
            rexp (-(r * sin φ) ^ 2 / 2)) * r ^ 3 * (max (cos φ) 0 * max (cos (φ - θ)) 0) := by
          ring
      _ = _ := by rw [ec, eb]; ring
  have hsp := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun r : ℝ => (2 * π)⁻¹ * (r ^ 3 * rexp (-(1 / 2) * r ^ 2)))
    (fun φ : ℝ => max (cos φ) 0 * max (cos (φ - θ)) 0) (Set.Ioi (0:ℝ)) (Set.Ioo (-π) π)
  beta_reduce at hsp
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hEq,
    Measure.volume_eq_prod, hsp, integral_const_mul, radial, angular h0 hπ]
  field_simp

/-- Cho–Saul formula for the ReLU pair average. -/
theorem gaussPairAvg_relu_main (s11 s12 s22 : ℝ) (h11 : 0 < s11) (h22 : 0 < s22)
    (h12 : s12 ^ 2 ≤ s11 * s22) :
    gaussPairAvg (fun t => max t 0) s11 s12 s22 =
      1 / (2 * π) * √(s11 * s22) *
        (sin (arccos (s12 / √(s11 * s22))) +
          (π - arccos (s12 / √(s11 * s22))) * cos (arccos (s12 / √(s11 * s22)))) := by
  set ρ := s12 / √(s11 * s22) with hρ
  set θ := arccos ρ with hθ
  have hS : 0 < √(s11 * s22) := Real.sqrt_pos.2 (mul_pos h11 h22)
  have hρ1 : |ρ| ≤ 1 := by
    rw [hρ, abs_div, abs_of_pos hS, div_le_one hS]
    exact Real.abs_le_sqrt h12
  have hc : cos θ = ρ := cos_arccos (by linarith [neg_abs_le ρ]) (by linarith [le_abs_self ρ])
  have ht0 : 0 ≤ θ := arccos_nonneg ρ
  have htπ : θ ≤ π := arccos_le_pi ρ
  have hsq : √s11 * √s22 = √(s11 * s22) := (Real.sqrt_mul h11.le s22).symm
  have hcs : √s11 * (√s22 * cos θ) = s12 := by
    rw [hc, hρ, ← mul_assoc, hsq]; field_simp
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![√s11, 0; √s22 * cos θ, √s22 * sin θ]
  have hAA : A * A.transpose = !![s11, s12; s12, s22] := by
    have e22 : √s22 * cos θ * (√s22 * cos θ) + √s22 * sin θ * (√s22 * sin θ) = s22 := by
      have := sin_sq_add_cos_sq θ
      have h2 := Real.mul_self_sqrt h22.le
      linear_combination (√s22 * √s22) * this + h2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Fin.sum_univ_two, Real.mul_self_sqrt h11.le, e22]
    · exact hcs
    · rw [mul_comm]; exact hcs
  have hmeas : Measurable (fun u : Fin 2 → ℝ => WithLp.toLp 2 (A.mulVec u)) :=
    ((PiLp.continuous_toLp 2 _).comp
      (Continuous.matrix_mulVec continuous_const continuous_id)).measurable
  have hF : Measurable (fun v : EuclideanSpace ℝ (Fin 2) => max (v 0) 0 * max (v 1) 0) :=
    (((PiLp.continuous_apply 2 _ 0).max continuous_const).mul
      ((PiLp.continuous_apply 2 _ 1).max continuous_const)).measurable
  unfold gaussPairAvg
  rw [← hAA, ← map_pi_gaussian_linear A, integral_map hmeas.aemeasurable hF.aestronglyMeasurable]
  have e : ∀ u : Fin 2 → ℝ, max ((WithLp.toLp 2 (A.mulVec u)) 0) 0 *
      max ((WithLp.toLp 2 (A.mulVec u)) 1) 0 =
      (√s11 * √s22) * (max (u 0) 0 * max (cos θ * u 0 + sin θ * u 1) 0) := by
    intro u
    have a0 : (WithLp.toLp 2 (A.mulVec u)) 0 = √s11 * u 0 := by
      simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have a1 : (WithLp.toLp 2 (A.mulVec u)) 1 = √s22 * (cos θ * u 0 + sin θ * u 1) := by
      simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
    rw [a0, a1, max_mul_of_nonneg (Real.sqrt_nonneg _), max_mul_of_nonneg (Real.sqrt_nonneg _)]
    ring
  simp_rw [e]
  rw [integral_const_mul, J_eq ht0 htπ, hsq]
  field_simp

end reluPair

end FW
end LesHouchesWidth

open MeasureTheory ProbabilityTheory LesHouchesWidth in
theorem solution (s11 s12 s22 : ℝ) (h11 : 0 < s11) (h22 : 0 < s22)
    (h12 : s12 ^ 2 ≤ s11 * s22) :
    gaussPairAvg (fun t => max t 0) s11 s12 s22 =
      1 / (2 * Real.pi) * Real.sqrt (s11 * s22) *
        (Real.sin (Real.arccos (s12 / Real.sqrt (s11 * s22))) +
          (Real.pi - Real.arccos (s12 / Real.sqrt (s11 * s22))) *
            Real.cos (Real.arccos (s12 / Real.sqrt (s11 * s22)))) := by
  exact FW.gaussPairAvg_relu_main s11 s12 s22 h11 h22 h12
