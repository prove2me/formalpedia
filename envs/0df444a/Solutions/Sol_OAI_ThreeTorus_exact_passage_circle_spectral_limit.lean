-- Prove2me | solution 1 for OAI.ThreeTorus.exact_passage_circle_spectral_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:09:05.174179+00:00
-- url     : https://prove2.me/submissions/291a5706-d585-4922-a651-47cb56d7fa25

import Mathlib
import Definitions.Def_OAIQ13Tt000

section
-- module Solutions.OAIQ13_TT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_StationaryPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform signed stationary phase, oscillatory integral estimates, and summed coefficient-mass control. -/

noncomputable section

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
namespace ThreeTorus

lemma quadratic_gaussian_pairing (f : 𝓢(ℝ, ℂ)) {b : ℂ} (hb : 0 < b.re) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2)) =
      (1 / b ^ (1 / 2 : ℂ)) * (∫ ξ : ℝ, (𝓕⁻ f) ξ *
        Complex.exp (-Real.pi / b * ξ ^ 2)) := by
  have hi : Integrable (fun x : ℝ => Complex.exp (-Real.pi * b * x ^ 2)) := by
    have hb' : 0 < ((Real.pi : ℂ) * b).re := by
      simpa only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] using mul_pos Real.pi_pos hb
    simpa only [neg_mul, mul_zero, zero_mul, add_zero] using
      integrable_cexp_quadratic hb' 0 0
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner (𝓕⁻ f).integrable hi
  have hinv : (𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) = (f : ℝ → ℂ) := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  have h' : (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2)) =
      ∫ x : ℝ, (𝓕⁻ f) x * (𝓕 fun y : ℝ => Complex.exp (-Real.pi * b * y ^ 2)) x := by
    rw [flip_innerₗ] at h
    change (∫ x : ℝ, (𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x •
      Complex.exp (-Real.pi * b * x ^ 2)) = _ at h
    simpa only [hinv, smul_eq_mul] using! h
  rw [h', fourier_gaussian_pi hb, ← integral_const_mul]
  congr 1
  ext x
  ring

lemma norm_quadratic_exp_le_one {b : ℂ} (hb : 0 ≤ b.re) (x : ℝ) :
    ‖Complex.exp (-(Real.pi : ℂ) * b * x ^ 2)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have he : (-(Real.pi : ℂ) * b * (x : ℂ) ^ 2).re = -Real.pi * b.re * x ^ 2 := by
    simp [mul_re, mul_im, pow_two]
  rw [he]
  have := mul_nonneg (mul_nonneg Real.pi_pos.le hb) (sq_nonneg x)
  linarith

/-- The Gaussian identity extends to the imaginary boundary after pairing with
an integrable Schwartz amplitude. This uses dominated convergence, never a
non-absolutely convergent Bochner integral for a bare Fresnel kernel. -/
lemma quadratic_boundary_pairing (f : 𝓢(ℝ, ℂ)) {b : ℂ}
    (hb : 0 ≤ b.re) (hbslit : b ∈ Complex.slitPlane) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2)) =
      (1 / b ^ (1 / 2 : ℂ)) * (∫ ξ : ℝ, (𝓕⁻ f) ξ *
        Complex.exp (-Real.pi / b * ξ ^ 2)) := by
  have hb0 : b ≠ 0 := Complex.slitPlane_ne_zero hbslit
  have hparam : Tendsto (fun ε : ℝ => b + (ε : ℂ)) (𝓝[>] 0) (𝓝 b) := by
    have hcast : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [add_zero] using hcast.const_add b
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hre : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < (b + (ε : ℂ)).re := by
    filter_upwards [heps] with ε hε
    simp only [add_re, ofReal_re]
    linarith
  have hleft : Tendsto (fun ε : ℝ => ∫ x : ℝ,
      f x * Complex.exp (-Real.pi * (b + (ε : ℂ)) * x ^ 2)) (𝓝[>] 0)
        (𝓝 (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
      ?_ ?_ f.integrable.norm ?_
    · exact Eventually.of_forall (fun ε => by apply Continuous.aestronglyMeasurable; fun_prop)
    · filter_upwards [hre] with ε hε
      filter_upwards [] with x
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (norm_quadratic_exp_le_one hε.le x)
        (norm_nonneg (f x))).trans_eq (mul_one _)
    · filter_upwards [] with x
      exact tendsto_const_nhds.mul (((hparam.const_mul _).mul_const _).cexp)
  have hintegral : Tendsto (fun ε : ℝ => ∫ x : ℝ,
      (𝓕⁻ f) x * Complex.exp (-Real.pi / (b + (ε : ℂ)) * x ^ 2)) (𝓝[>] 0)
        (𝓝 (∫ x : ℝ, (𝓕⁻ f) x * Complex.exp (-Real.pi / b * x ^ 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖(𝓕⁻ f) x‖)
      ?_ ?_ (𝓕⁻ f).integrable.norm ?_
    · exact Eventually.of_forall (fun ε => by apply Continuous.aestronglyMeasurable; fun_prop)
    · filter_upwards [hre] with ε hε
      filter_upwards [] with x
      rw [norm_mul, div_eq_mul_inv]
      have hb' : 0 ≤ (b + (ε : ℂ))⁻¹.re := by
        rw [Complex.inv_re]
        exact div_nonneg hε.le (Complex.normSq_nonneg _)
      exact (mul_le_mul_of_nonneg_left (norm_quadratic_exp_le_one hb' x)
        (norm_nonneg ((𝓕⁻ f) x))).trans_eq (mul_one _)
    · filter_upwards [] with x
      exact tendsto_const_nhds.mul (((tendsto_const_nhds.div hparam hb0).mul_const _).cexp)
  have hpow : Tendsto (fun ε : ℝ => 1 / (b + (ε : ℂ)) ^ (1 / 2 : ℂ))
      (𝓝[>] 0) (𝓝 (1 / b ^ (1 / 2 : ℂ))) := by
    apply tendsto_const_nhds.div
    · exact (continuousAt_cpow_const hbslit).tendsto.comp hparam
    · exact cpow_ne_zero_iff.mpr (Or.inl hb0)
  have hr := hpow.mul hintegral
  have hright := hr.congr' (hre.mono (fun ε hε => (quadratic_gaussian_pairing f hε).symm))
  exact tendsto_nhds_unique hleft hright

lemma cpow_pos_mul {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((t : ℂ) * z) ^ w = (t : ℂ) ^ w * z ^ w := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr ht.ne') hz),
    Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'),
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul ht hz,
    ← Complex.ofReal_log ht.le, add_mul, Complex.exp_add]

lemma quadratic_factor {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t : ℂ) / ((t : ℂ) * (-I)) ^ (1 / 2 : ℂ) =
      Complex.exp ((Real.pi : ℂ) / 4 * I) := by
  have hs : (Real.sqrt t : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le]
    norm_num
  rw [cpow_pos_mul ht (neg_ne_zero.mpr I_ne_zero), hs, div_mul_eq_div_div,
    div_self (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr ht.ne'))),
    Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero), Complex.log_neg_I,
    one_div, ← Complex.exp_neg]
  congr 1
  ring

lemma integral_fourierInv (f : 𝓢(ℝ, ℂ)) : (∫ x : ℝ, (𝓕⁻ f) x) = f 0 := by
  have he : (𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) 0 = f 0 := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  simpa [Real.fourier_eq] using he

lemma quadratic_stationary_identity (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t : ℂ) * (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) =
      Complex.exp ((Real.pi : ℂ) / 4 * I) *
        (∫ ξ : ℝ, (𝓕⁻ f) ξ * Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ))) := by
  have hb : 0 ≤ ((t : ℂ) * (-I)).re := by simp
  have hslit : (t : ℂ) * (-I) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simpa using ht.ne'
  have he := quadratic_boundary_pairing f hb hslit
  have hleft : ∀ x : ℝ, Complex.exp (-(Real.pi : ℂ) * ((t : ℂ) * (-I)) * x^2) =
      Complex.exp (I * (Real.pi * t * x^2 : ℝ)) := by
    intro x
    congr 1
    push_cast
    ring
  have hright : ∀ x : ℝ, Complex.exp (-(Real.pi : ℂ) / ((t : ℂ) * (-I)) * x^2) =
      Complex.exp (I * (-Real.pi / t * x^2 : ℝ)) := by
    intro x
    congr 1
    push_cast
    field_simp
    simp [I_sq]
    ring
  simp only [hleft, hright] at he
  rw [he, ← mul_assoc, ← div_eq_mul_one_div, quadratic_factor ht]

lemma quadratic_stationary_error (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    ‖(Real.sqrt t : ℂ) * (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) -
      Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0‖ ≤
        (Real.pi / t) * (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ f) ξ‖) := by
  rw [quadratic_stationary_identity f ht, ← mul_sub, norm_mul]
  have hnorm : ‖Complex.exp ((Real.pi : ℂ) / 4 * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hnorm, one_mul, ← integral_fourierInv f]
  have hi : Integrable (fun ξ : ℝ => (𝓕⁻ f) ξ *
      Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ))) := by
    apply ((𝓕⁻ f).integrable (μ := volume)).mul_bdd
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards [] with ξ
      have he : ‖Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ))‖ = 1 := by
        rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
      exact he.le
  rw [← integral_sub hi (𝓕⁻ f).integrable]
  have hd : Integrable (fun ξ : ℝ => ξ^2 * ‖(𝓕⁻ f) ξ‖) := by
    have hh := (𝓕⁻ f).integrable_pow_mul volume 2
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hd.const_mul (Real.pi / t))
  filter_upwards [] with ξ
  have heq : (𝓕⁻ f) ξ * Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - (𝓕⁻ f) ξ =
      (𝓕⁻ f) ξ * (Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - 1) := by ring
  rw [heq, norm_mul]
  have he := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -Real.pi / t * ξ^2)
  have he' : ‖Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - 1‖ ≤
      Real.pi / t * ξ^2 := by
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos Real.pi_pos,
      abs_of_pos ht, abs_of_nonneg (sq_nonneg ξ)]
  calc
    ‖(𝓕⁻ f) ξ‖ * ‖Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - 1‖ ≤
        ‖(𝓕⁻ f) ξ‖ * (Real.pi / t * ξ^2) :=
      mul_le_mul_of_nonneg_left he' (norm_nonneg _)
    _ = _ := by ring

lemma quadratic_stationary_limit (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
        (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ)))) atTop
      (𝓝 (Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0)) := by
  have hlim : Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
      (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) -
        Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact quadratic_stationary_error f ht
    · simpa using (tendsto_const_nhds.div_atTop tendsto_id).mul_const
        (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ f) ξ‖)
  simpa using hlim.add_const (Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0)

lemma quadratic_stationary_compact {f : ℝ → ℂ} (hf : HasCompactSupport f)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
        (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ)))) atTop
      (𝓝 (Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0)) :=
  quadratic_stationary_limit (hf.toSchwartzMap hsm)

lemma oscillatory_integral_parts {a b t : ℝ} (ht : t ≠ 0)
    {φ φ' : ℝ → ℝ} {B B' : ℝ → ℂ}
    (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (φ' x) x)
    (hB : ∀ x ∈ uIcc a b, HasDerivAt B (B' x) x)
    (hφ' : ContinuousOn φ' (uIcc a b))
    (hB' : IntervalIntegrable B' volume a b) :
    (∫ x in a..b, B x * (φ' x : ℂ) * Complex.exp (I * (t * φ x : ℝ))) =
      (1 / (I * (t : ℂ))) *
        (B b * Complex.exp (I * (t * φ b : ℝ)) -
          B a * Complex.exp (I * (t * φ a : ℝ)) -
            ∫ x in a..b, B' x * Complex.exp (I * (t * φ x : ℝ))) := by
  have hv (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun x => Complex.exp (I * (t * φ x : ℝ)))
        (Complex.exp (I * (t * φ x : ℝ)) * (I * (t * φ' x : ℝ))) x := by
    exact (((hφ x hx).const_mul t).ofReal_comp.const_mul I).cexp
  have hφc : ContinuousOn φ (uIcc a b) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hvi : IntervalIntegrable
      (fun x => Complex.exp (I * (t * φ x : ℝ)) * (I * (t * φ' x : ℝ))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul hB hv hB' hvi
  have hj : (∫ x in a..b, B x * (Complex.exp (I * (t * φ x : ℝ)) *
      (I * (t * φ' x : ℝ)))) = (I * (t : ℂ)) *
        (∫ x in a..b, B x * (φ' x : ℂ) * Complex.exp (I * (t * φ x : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    push_cast
    ring
  rw [hj] at he
  rw [← he]
  field_simp [ofReal_ne_zero.mpr ht]

lemma oscillatory_integral_bound {a b t : ℝ} (hab : a ≤ b) (ht : t ≠ 0)
    {φ φ' : ℝ → ℝ} {B B' : ℝ → ℂ}
    (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (φ' x) x)
    (hB : ∀ x ∈ uIcc a b, HasDerivAt B (B' x) x)
    (hφ' : ContinuousOn φ' (uIcc a b))
    (hB' : IntervalIntegrable B' volume a b) :
    ‖∫ x in a..b, B x * (φ' x : ℂ) * Complex.exp (I * (t * φ x : ℝ))‖ ≤
      (1 / |t|) * (‖B b‖ + ‖B a‖ + ∫ x in a..b, ‖B' x‖) := by
  rw [oscillatory_integral_parts ht hφ hB hφ' hB', norm_mul]
  have he (r : ℝ) : ‖Complex.exp (I * (r : ℂ))‖ = 1 := by
    rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
  have hc : ‖1 / (I * (t : ℂ))‖ = 1 / |t| := by simp
  rw [hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖B b * Complex.exp (I * (t * φ b : ℝ)) -
      B a * Complex.exp (I * (t * φ a : ℝ)) -
        ∫ x in a..b, B' x * Complex.exp (I * (t * φ x : ℝ))‖ ≤
      ‖B b * Complex.exp (I * (t * φ b : ℝ)) -
        B a * Complex.exp (I * (t * φ a : ℝ))‖ +
          ‖∫ x in a..b, B' x * Complex.exp (I * (t * φ x : ℝ))‖ := norm_sub_le _ _
    _ ≤ (‖B b‖ + ‖B a‖) + ∫ x in a..b, ‖B' x‖ := by
      apply add_le_add
      · simpa only [norm_mul, he, mul_one] using
          norm_sub_le (B b * Complex.exp (I * (t * φ b : ℝ)))
            (B a * Complex.exp (I * (t * φ a : ℝ)))
      · simpa only [norm_mul, he, mul_one] using
          intervalIntegral.norm_integral_le_integral_norm hab
            (f := fun x => B' x * Complex.exp (I * (t * φ x : ℝ)))

lemma reciprocal_variation {a b r : ℝ} (hab : a ≤ b) (hr : 0 < r)
    {q q' : ℝ → ℝ}
    (hq : ∀ x ∈ Icc a b, HasDerivAt q (q' x) x)
    (hqc : ContinuousOn q' (Icc a b))
    (hsep : ∀ x ∈ Icc a b, r ≤ |q x|) :
    (∫ x in a..b, q' x / q x ^ 2) = (q a)⁻¹ - (q b)⁻¹ ∧
      (∫ x in a..b, q' x / q x ^ 2) ≤ 2 / r := by
  have hne (x : ℝ) (hx : x ∈ Icc a b) : q x ≠ 0 := by
    intro hz
    have := hsep x hx
    simp only [hz, abs_zero] at this
    linarith
  have hc : ContinuousOn q (Icc a b) :=
    fun x hx => (hq x hx).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun x => q' x / q x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hqc.div (hc.pow 2) (fun x hx => pow_ne_zero _ (hne x hx))
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x => -(q x)⁻¹) (q' x / q x ^ 2) x := by
    rw [uIcc_of_le hab]
    intro x hx
    simpa only [Pi.neg_apply, Pi.inv_apply, neg_div, neg_neg] using!
      ((hq x hx).inv (hne x hx)).neg
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simp only [sub_neg_eq_add, neg_add_eq_sub] at he
  refine ⟨he, ?_⟩
  rw [he]
  have bound (x : ℝ) (hx : x ∈ Icc a b) : |(q x)⁻¹| ≤ 1 / r := by
    rw [abs_inv, one_div]
    exact inv_anti₀ hr (hsep x hx)
  calc
    (q a)⁻¹ - (q b)⁻¹ ≤ |(q a)⁻¹| + |(q b)⁻¹| := by
      linarith [le_abs_self ((q a)⁻¹), neg_le_abs ((q b)⁻¹)]
    _ ≤ 1 / r + 1 / r := add_le_add (bound a ⟨le_rfl, hab⟩) (bound b ⟨hab, le_rfl⟩)
    _ = 2 / r := by ring

lemma nonstationary_monotone_bound {a b t r C₀ C₁ : ℝ}
    (hab : a ≤ b) (ht : t ≠ 0) (hr : 0 < r) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    {φ q q' : ℝ → ℝ} {A A' : ℝ → ℂ}
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (q x) x)
    (hq : ∀ x ∈ Icc a b, HasDerivAt q (q' x) x)
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hqc : ContinuousOn q' (Icc a b)) (hAc : ContinuousOn A' (Icc a b))
    (hqpos : ∀ x ∈ Icc a b, 0 ≤ q' x)
    (hsep : ∀ x ∈ Icc a b, r ≤ |q x|)
    (hAb : ∀ x ∈ Icc a b, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc a b, ‖A' x‖ ≤ C₁) :
    ‖∫ x in a..b, A x * Complex.exp (I * (t * φ x : ℝ))‖ ≤
      (4 * C₀ + (b - a) * C₁) / (|t| * r) := by
  have hne (x : ℝ) (hx : x ∈ Icc a b) : q x ≠ 0 := by
    intro hz
    have := hsep x hx
    simp only [hz, abs_zero] at this
    linarith
  have hc : ContinuousOn q (Icc a b) :=
    fun x hx => (hq x hx).continuousAt.continuousWithinAt
  have hAf : ContinuousOn A (Icc a b) :=
    fun x hx => (hA x hx).continuousAt.continuousWithinAt
  let B := fun x => A x / (q x : ℂ)
  let B' := fun x => A' x / (q x : ℂ) - A x * (q' x / q x ^ 2 : ℝ)
  have hB : ∀ x ∈ uIcc a b, HasDerivAt B (B' x) x := by
    rw [uIcc_of_le hab]
    intro x hx
    have he : B' x = (A' x * (q x : ℂ) - A x * (q' x : ℂ)) / (q x : ℂ)^2 := by
      dsimp only [B']
      push_cast
      field_simp [ofReal_ne_zero.mpr (hne x hx)]
    rw [he]
    exact (hA x hx).div (hq x hx).ofReal_comp (ofReal_ne_zero.mpr (hne x hx))
  have hBc : ContinuousOn B' (Icc a b) := by
    dsimp [B']
    exact (hAc.div (Complex.continuous_ofReal.comp_continuousOn hc) (fun x hx => ofReal_ne_zero.mpr (hne x hx))).sub
      (hAf.mul (Complex.continuous_ofReal.comp_continuousOn
        (hqc.div (hc.pow 2) (fun x hx => pow_ne_zero _ (hne x hx)))))
  have hBi : IntervalIntegrable B' volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hBc
  have hbound (x : ℝ) (hx : x ∈ Icc a b) : ‖B x‖ ≤ C₀ / r := by
    dsimp [B]
    rw [norm_div, norm_real, Real.norm_eq_abs]
    exact div_le_div₀ hC₀ (hAb x hx) hr (hsep x hx)
  have hbound' (x : ℝ) (hx : x ∈ Icc a b) :
      ‖B' x‖ ≤ C₁ / r + C₀ * (q' x / q x ^ 2) := by
    dsimp [B']
    calc
      ‖A' x / (q x : ℂ) - A x * (q' x / q x ^ 2 : ℝ)‖ ≤
        ‖A' x / (q x : ℂ)‖ + ‖A x * (q' x / q x ^ 2 : ℝ)‖ := norm_sub_le _ _
      _ ≤ C₁ / r + C₀ * (q' x / q x ^ 2) := by
        apply add_le_add
        · rw [norm_div, norm_real, Real.norm_eq_abs]
          exact div_le_div₀ hC₁ (hA'b x hx) hr (hsep x hx)
        · rw [norm_mul, norm_real, Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (hqpos x hx) (sq_nonneg _))]
          exact mul_le_mul_of_nonneg_right (hAb x hx)
            (div_nonneg (hqpos x hx) (sq_nonneg _))
  have hiq : IntervalIntegrable (fun x => q' x / q x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hqc.div (hc.pow 2) (fun x hx => pow_ne_zero _ (hne x hx))
  have hint : (∫ x in a..b, ‖B' x‖) ≤ (b - a) * (C₁ / r) + C₀ * (2 / r) := by
    calc
      (∫ x in a..b, ‖B' x‖) ≤ (∫ x in a..b, C₁ / r + C₀ * (q' x / q x ^ 2)) :=
        intervalIntegral.integral_mono_on hab hBi.norm
          ((intervalIntegrable_const).add (hiq.const_mul C₀)) hbound'
      _ = (b - a) * (C₁ / r) + C₀ * (∫ x in a..b, q' x / q x ^ 2) := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hiq.const_mul C₀),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left
        (reciprocal_variation hab hr hq hqc hsep).2 hC₀) _
  have heq : (∫ x in a..b, B x * (q x : ℂ) * Complex.exp (I * (t * φ x : ℝ))) =
      (∫ x in a..b, A x * Complex.exp (I * (t * φ x : ℝ))) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    intro x hx
    simp only [B, div_mul_cancel₀ (A x) (ofReal_ne_zero.mpr (hne x hx))]
  have hh := oscillatory_integral_bound hab ht
    (φ := φ) (φ' := q) (B := B) (B' := B')
    (by simpa only [uIcc_of_le hab] using hφ) hB
    (by simpa only [uIcc_of_le hab] using hc) hBi
  rw [heq] at hh
  calc
    _ ≤ _ := hh
    _ ≤ (1 / |t|) * (C₀ / r + C₀ / r + ((b-a) * (C₁/r) + C₀ * (2/r))) := by
      gcongr
      · exact hbound b ⟨hab, le_rfl⟩
      · exact hbound a ⟨le_rfl, hab⟩
    _ = _ := by ring

lemma cubic_taylor_estimate {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ)
    {v x M : ℝ} (hv : deriv φ v = 0)
    (hM : ∀ u ∈ uIcc v x, |iteratedDeriv 3 φ u| ≤ M) :
    |φ x - φ v - (iteratedDeriv 2 φ v) / 2 * (x - v)^2| ≤
      M * |x - v|^3 / 6 := by
  by_cases h : v = x
  · subst x
    simp
  have hu := uniqueDiffOn_uIcc h
  have ht : taylorWithinEval φ 2 (uIcc v x) v x =
      φ v + (iteratedDeriv 2 φ v) / 2 * (x - v)^2 := by
    rw [taylorWithinEval_succ φ 1, taylorWithinEval_succ φ 0, taylor_within_zero_eval]
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hφ.of_le (by norm_num)).contDiffAt (left_mem_uIcc),
      iteratedDerivWithin_eq_iteratedDeriv hu (hφ.of_le (by norm_num)).contDiffAt (left_mem_uIcc)]
    simp only [iteratedDeriv_one, hv, zero_add, Nat.factorial_zero, Nat.factorial_one,
      Nat.cast_one, Nat.cast_zero, one_mul, pow_one, smul_eq_mul, mul_zero, add_zero]
    ring
  obtain ⟨u, hu', he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) h hφ.contDiffOn
  rw [ht] at he
  have hu'' : u ∈ uIcc v x := ⟨hu'.1.le, hu'.2.le⟩
  norm_num at he
  rw [show φ x - φ v - iteratedDeriv 2 φ v / 2 * (x-v)^2 =
    φ x - (φ v + iteratedDeriv 2 φ v / 2 * (x-v)^2) by ring, he,
      abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hM u hu'') (by positivity)) (by norm_num)

lemma norm_exp_imag_sub_le (s t : ℝ) :
    ‖Complex.exp (I * (s : ℂ)) - Complex.exp (I * (t : ℂ))‖ ≤ |s - t| := by
  have he : Complex.exp (I * (s : ℂ)) - Complex.exp (I * (t : ℂ)) =
      Complex.exp (I * (t : ℂ)) * (Complex.exp (I * ((s - t : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := s-t)

lemma local_stationary_comparison {φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hφ : ContDiff ℝ 3 φ) (hA : ContDiff ℝ 1 A)
    {r t C₀ C₁ M : ℝ} (hr : 0 ≤ r) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : φ 0 = 0) (hcrit : deriv φ 0 = 0) (hsecond : iteratedDeriv 2 φ 0 = 2 * Real.pi)
    (hM : ∀ x ∈ Icc (-r) r, |iteratedDeriv 3 φ x| ≤ M)
    (hAb : ‖A 0‖ ≤ C₀) (hA'b : ∀ x ∈ Icc (-r) r, ‖deriv A x‖ ≤ C₁) :
    ‖(∫ x in -r..r, A x * Complex.exp (I * (t * φ x : ℝ))) -
        A 0 * (∫ x in -r..r, Complex.exp (I * (Real.pi * t * x^2 : ℝ)))‖ ≤
      2 * r * (C₁ * r + C₀ * (|t| * M * r^3 / 6)) := by
  have h0 : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr⟩
  have ha (x : ℝ) (hx : x ∈ Icc (-r) r) : ‖A x - A 0‖ ≤ C₁ * r := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hA.differentiable (by norm_num) x) hA'b (convex_Icc (-r) r) h0 hx
    simp only [sub_zero, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_le.mpr hx) hC₁)
  have hp (x : ℝ) (hx : x ∈ Icc (-r) r) : |φ x - Real.pi * x^2| ≤ M * r^3 / 6 := by
    have h := cubic_taylor_estimate hφ hcrit (fun u hu => hM u (uIcc_subset_Icc h0 hx hu))
    simp only [hzero, hsecond, sub_zero, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at h
    calc
      |φ x - Real.pi * x^2| ≤ M * |x|^3 / 6 := by convert h using 1
      _ ≤ _ := by gcongr; exact abs_le.mpr hx
  have hc₁ : IntervalIntegrable (fun x => A x * Complex.exp (I * (t * φ x : ℝ))) volume (-r) r := by
    apply Continuous.intervalIntegrable
    have := hA.continuous
    have := hφ.continuous
    fun_prop
  have hc₂ : IntervalIntegrable (fun x => A 0 * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) volume (-r) r := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hc₁ hc₂]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -r) (b := r) (C := C₁*r + C₀*(|t| *M*r^3/6))
    (f := fun x => A x * Complex.exp (I * (t * φ x : ℝ)) -
      A 0 * Complex.exp (I * (Real.pi * t * x^2 : ℝ)))
  have hpoint (x : ℝ) (hx : x ∈ Icc (-r) r) :
      ‖A x * Complex.exp (I * (t * φ x : ℝ)) -
        A 0 * Complex.exp (I * (Real.pi * t * x^2 : ℝ))‖ ≤
          C₁*r + C₀*(|t| *M*r^3/6) := by
    have heq : A x * Complex.exp (I * (t * φ x : ℝ)) -
        A 0 * Complex.exp (I * (Real.pi * t * x^2 : ℝ)) =
        (A x - A 0) * Complex.exp (I * (t * φ x : ℝ)) +
        A 0 * (Complex.exp (I * (t * φ x : ℝ)) -
          Complex.exp (I * (Real.pi * t * x^2 : ℝ))) := by ring
    rw [heq]
    calc
      _ ≤ ‖(A x - A 0) * Complex.exp (I * (t * φ x : ℝ))‖ +
        ‖A 0 * (Complex.exp (I * (t * φ x : ℝ)) -
          Complex.exp (I * (Real.pi * t * x^2 : ℝ)))‖ := norm_add_le _ _
      _ ≤ C₁*r + C₀*(|t| *M*r^3/6) := by
        apply add_le_add
        · rw [norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, mul_one]
          exact ha x hx
        · rw [norm_mul]
          apply mul_le_mul hAb _ (norm_nonneg _) hC₀
          calc
            _ ≤ |t * φ x - Real.pi * t * x^2| := norm_exp_imag_sub_le _ _
            _ = |t| * |φ x - Real.pi * x^2| := by rw [← abs_mul]; congr 1; ring
            _ ≤ |t| * (M*r^3/6) := mul_le_mul_of_nonneg_left (hp x hx) (abs_nonneg _)
            _ = _ := by ring
  specialize hh (fun x hx => hpoint x (by
    rw [uIoc_of_le (by linarith : -r ≤ r)] at hx
    exact ⟨hx.1.le, hx.2⟩))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_of_nonneg (by linarith : 0 ≤ r - -r)]
  ring

lemma derivative_coercive {q : ℝ → ℝ} {R c : ℝ}
    (hR : 0 ≤ R) (hq : Differentiable ℝ q) (hq0 : q 0 = 0)
    (hc : ∀ x ∈ Icc (-R) R, c ≤ deriv q x) :
    ∀ x ∈ Icc (-R) R, c * |x| ≤ |q x| := by
  intro x hx
  have h := (convex_Icc (-R) R).mul_sub_le_image_sub_of_le_deriv
    hq.continuous.continuousOn hq.differentiableOn
    (fun x hx => hc x (interior_subset hx))
  have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR⟩
  rcases le_total 0 x with hp | hn
  · have hh := h 0 h0 x hx hp
    rw [hq0, sub_zero, sub_zero] at hh
    rw [abs_of_nonneg hp]
    exact hh.trans (le_abs_self _)
  · have hh := h x hx 0 h0 hn
    rw [hq0, zero_sub, zero_sub] at hh
    rw [abs_of_nonpos hn]
    exact hh.trans (neg_le_abs _)

lemma normalized_phase_tail {φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hφ : ContDiff ℝ 3 φ) (hA : ContDiff ℝ 2 A)
    {a b R c r t C₀ C₁ : ℝ}
    (hab : a ≤ b) (ha : -R ≤ a) (hb : b ≤ R) (ht : t ≠ 0) (hr : 0 < r)
    (hc : 0 < c) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hcrit : deriv φ 0 = 0)
    (hsecond : ∀ x ∈ Icc (-R) R, c ≤ iteratedDeriv 2 φ x)
    (hsep : ∀ x ∈ Icc a b, r ≤ |x|)
    (hAb : ∀ x ∈ Icc (-R) R, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc (-R) R, ‖deriv A x‖ ≤ C₁) :
    ‖∫ x in a..b, A x * Complex.exp (I * (t * φ x : ℝ))‖ ≤
      (4 * C₀ + 2 * R * C₁) / (|t| * (c * r)) := by
  have hR : 0 ≤ R := by linarith
  have hsub : Icc a b ⊆ Icc (-R) R := Icc_subset_Icc ha hb
  have hq : ContDiff ℝ 2 (deriv φ) := by simpa using (hφ.of_le (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).deriv'
  have hqa : Differentiable ℝ (deriv φ) := hq.differentiable (by norm_num)
  have hd : ∀ x, deriv (deriv φ) x = iteratedDeriv 2 φ x := by
    intro x
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hco := derivative_coercive hR hqa hcrit (by simpa only [hd] using hsecond)
  have h := nonstationary_monotone_bound hab ht (mul_pos hc hr) hC₀ hC₁
    (φ := φ) (q := deriv φ) (q' := deriv (deriv φ)) (A := A) (A' := deriv A)
    (fun x _ => (hφ.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hqa x).hasDerivAt)
    (fun x _ => (hA.differentiable (by norm_num) x).hasDerivAt)
    (hq.continuous_deriv (by norm_num)).continuousOn
    (hA.continuous_deriv (by norm_num)).continuousOn
    (fun x hx => hc.le.trans (by simpa only [hd] using hsecond x (hsub hx)))
    (fun x hx => (mul_le_mul_of_nonneg_left (hsep x hx) hc.le).trans (hco x (hsub hx)))
    (fun x hx => hAb x (hsub hx)) (fun x hx => hA'b x (hsub hx))
  refine h.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  gcongr
  linarith

lemma quadratic_phase_deriv (x : ℝ) : deriv (fun x : ℝ => Real.pi*x^2) x = 2*Real.pi*x := by
  convert ((hasDerivAt_id x).pow 2).const_mul Real.pi |>.deriv using 1 <;>
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, mul_one]; ring

lemma quadratic_phase_second (x : ℝ) : iteratedDeriv 2 (fun x : ℝ => Real.pi*x^2) x = 2*Real.pi := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [show deriv (fun x : ℝ => Real.pi*x^2) = fun x => 2*Real.pi*x from funext quadratic_phase_deriv]
  exact ((hasDerivAt_id x).const_mul (2*Real.pi)).deriv.trans (mul_one _)

lemma interval_three_parts {F : ℝ → ℂ} (hF : Continuous F) (R r : ℝ) :
    (∫ x in -R..R, F x) = ((∫ x in -R..-r, F x) + (∫ x in -r..r, F x)) +
      (∫ x in r..R, F x) := by
  rw [intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)]

lemma stationary_interval_comparison {φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hφ : ContDiff ℝ 3 φ) (hA : ContDiff ℝ 2 A)
    {R c r t C₀ C₁ M : ℝ} (hr : 0 < r) (hrR : r ≤ R) (ht : t ≠ 0)
    (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : φ 0 = 0) (hcrit : deriv φ 0 = 0)
    (hsecond0 : iteratedDeriv 2 φ 0 = 2 * Real.pi)
    (hsecond : ∀ x ∈ Icc (-R) R, c ≤ iteratedDeriv 2 φ x)
    (hM : ∀ x ∈ Icc (-R) R, |iteratedDeriv 3 φ x| ≤ M)
    (hAb : ∀ x ∈ Icc (-R) R, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc (-R) R, ‖deriv A x‖ ≤ C₁) :
    ‖(∫ x in -R..R, A x * Complex.exp (I * (t * φ x : ℝ))) -
        A 0 * (∫ x in -R..R, Complex.exp (I * (Real.pi * t * x^2 : ℝ)))‖ ≤
      2 * r * (C₁ * r + C₀ * (|t| * M * r^3 / 6)) +
        4 * ((4*C₀ + 2*R*C₁) / (|t| * (c*r))) := by
  have hR : 0 ≤ R := hr.le.trans hrR
  have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR⟩
  have hsub : Icc (-r) r ⊆ Icc (-R) R := Icc_subset_Icc (neg_le_neg hrR) hrR
  let F : ℝ → ℂ := fun x => A x * Complex.exp (I * (t * φ x : ℝ))
  let Q : ℝ → ℂ := fun x => A 0 * Complex.exp (I * (t * (Real.pi * x^2) : ℝ))
  let K := (4*C₀ + 2*R*C₁) / (|t| * (c*r))
  have hFc : Continuous F := by have := hA.continuous; have := hφ.continuous; fun_prop
  have hQc : Continuous Q := by fun_prop
  have hFL : ‖∫ x in -R..-r, F x‖ ≤ K :=
    normalized_phase_tail hφ hA (neg_le_neg hrR) le_rfl (by linarith) ht hr hc hC₀ hC₁
      hcrit hsecond (fun x hx => by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2]) hAb hA'b
  have hFR : ‖∫ x in r..R, F x‖ ≤ K :=
    normalized_phase_tail hφ hA hrR (by linarith) le_rfl ht hr hc hC₀ hC₁
      hcrit hsecond (fun x hx => (le_abs_self x).trans' hx.1) hAb hA'b
  have hqsm : ContDiff ℝ 3 (fun x : ℝ => Real.pi*x^2) := by fun_prop
  have hq0 : deriv (fun x : ℝ => Real.pi*x^2) 0 = 0 := by rw [quadratic_phase_deriv]; ring
  have hqsec : ∀ x ∈ Icc (-R) R, c ≤ iteratedDeriv 2 (fun x : ℝ => Real.pi*x^2) x := by
    intro x _; rwa [quadratic_phase_second]
  have hB : ContDiff ℝ 2 (fun _ : ℝ => A 0) := contDiff_const
  have hBb : ∀ x ∈ Icc (-R) R, ‖(fun _ : ℝ => A 0) x‖ ≤ C₀ := fun _ _ => hAb 0 h0
  have hB'b : ∀ x ∈ Icc (-R) R, ‖deriv (fun _ : ℝ => A 0) x‖ ≤ C₁ := by
    intro x _; simpa using hC₁
  have hQL : ‖∫ x in -R..-r, Q x‖ ≤ K :=
    normalized_phase_tail hqsm hB (neg_le_neg hrR) le_rfl (by linarith) ht hr hc hC₀ hC₁
      hq0 hqsec (fun x hx => by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2]) hBb hB'b
  have hQR : ‖∫ x in r..R, Q x‖ ≤ K :=
    normalized_phase_tail hqsm hB hrR (by linarith) le_rfl ht hr hc hC₀ hC₁
      hq0 hqsec (fun x hx => (le_abs_self x).trans' hx.1) hBb hB'b
  have hlocal := local_stationary_comparison hφ (hA.of_le (by norm_num))
    hr.le hC₀ hC₁ hM₀ hzero hcrit hsecond0
    (fun x hx => hM x (hsub hx)) (hAb 0 h0) (fun x hx => hA'b x (hsub hx)) (t := t)
  have heQ (a b : ℝ) : (∫ x in a..b, Q x) =
      A 0 * (∫ x in a..b, Complex.exp (I * (Real.pi * t * x^2 : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _; dsimp [Q]; congr 3; ring_nf
  rw [← heQ, interval_three_parts hFc R r, interval_three_parts hQc R r]
  rw [← heQ (-r) r] at hlocal
  have he : ((∫ x in -R..-r, F x) + (∫ x in -r..r, F x) + (∫ x in r..R, F x)) -
      ((∫ x in -R..-r, Q x) + (∫ x in -r..r, Q x) + (∫ x in r..R, Q x)) =
      ((∫ x in -r..r, F x) - (∫ x in -r..r, Q x)) +
        ((∫ x in -R..-r, F x) - (∫ x in -R..-r, Q x)) +
        ((∫ x in r..R, F x) - (∫ x in r..R, Q x)) := by ring
  rw [he]
  calc
    _ ≤ (‖(∫ x in -r..r, F x) - (∫ x in -r..r, Q x)‖ +
      ‖(∫ x in -R..-r, F x) - (∫ x in -R..-r, Q x)‖) +
      ‖(∫ x in r..R, F x) - (∫ x in r..R, Q x)‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (2*r*(C₁*r+C₀*(|t| *M*r^3/6)) + (K+K)) + (K+K) := by
      exact add_le_add (add_le_add hlocal ((norm_sub_le _ _).trans (add_le_add hFL hQL)))
        ((norm_sub_le _ _).trans (add_le_add hFR hQR))
    _ = _ := by dsimp [K]; ring

lemma stationary_interval_scaled_comparison {φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hφ : ContDiff ℝ 3 φ) (hA : ContDiff ℝ 2 A)
    {R c s C₀ C₁ M : ℝ} (hs : 0 < s) (hrR : 1/s^4 ≤ R)
    (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : φ 0 = 0) (hcrit : deriv φ 0 = 0)
    (hsecond0 : iteratedDeriv 2 φ 0 = 2 * Real.pi)
    (hsecond : ∀ x ∈ Icc (-R) R, c ≤ iteratedDeriv 2 φ x)
    (hM : ∀ x ∈ Icc (-R) R, |iteratedDeriv 3 φ x| ≤ M)
    (hAb : ∀ x ∈ Icc (-R) R, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc (-R) R, ‖deriv A x‖ ≤ C₁) :
    ‖(Real.sqrt (s^10) : ℂ) * ((∫ x in -R..R, A x * Complex.exp (I * (s^10 * φ x : ℝ))) -
        A 0 * (∫ x in -R..R, Complex.exp (I * (Real.pi * s^10 * x^2 : ℝ))))‖ ≤
      2*C₁/s^3 + C₀*M/(3*s) + 4*(4*C₀+2*R*C₁)/(c*s) := by
  have he : Real.sqrt (s^10) = s^5 := by
    rw [show s^10 = (s^5)^2 by ring, Real.sqrt_sq (by positivity)]
  rw [norm_mul, norm_real, Real.norm_eq_abs, he, abs_of_pos (pow_pos hs 5)]
  have h := stationary_interval_comparison hφ hA (by positivity : 0 < 1/s^4) hrR
    (pow_ne_zero 10 hs.ne') hc hπ hC₀ hC₁ hM₀ hzero hcrit hsecond0 hsecond hM hAb hA'b
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ s^5)
  refine hh.trans_eq ?_
  rw [abs_of_pos (pow_pos hs 10)]
  field_simp
  ring

lemma stationary_interval_comparison_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : ∀ a, φ a 0 = 0) (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = 2 * Real.pi)
    (hsecond : ∀ a x, x ∈ Icc (-R) R → c ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      ((∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
        A a 0 * (∫ x in -R..R, Complex.exp (I * (Real.pi * t * x^2 : ℝ)))))
      (fun _ => 0) atTop := by
  let s : ℝ → ℝ := fun t => t ^ ((10 : ℝ)⁻¹)
  have hst : Tendsto s atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hr : Tendsto (fun t : ℝ => 1/(s t)^4) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp hst)
  have hlim : Tendsto (fun t : ℝ =>
      2*C₁/(s t)^3 + C₀*M/(3*(s t)) + 4*(4*C₀+2*R*C₁)/(c*(s t))) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun t => 2*C₁/(s t)^3) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hst)
    have h₂ : Tendsto (fun t => C₀*M/(3*(s t))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3) hst)
    have h₃ : Tendsto (fun t => 4*(4*C₀+2*R*C₁)/(c*(s t))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hc hst)
    simpa only [add_zero] using Tendsto.add (Tendsto.add h₁ h₂) h₃
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ), hr.eventually (gt_mem_nhds hR),
    hlim.eventually (gt_mem_nhds hε)] with t ht htR htε
  intro a
  have hs : 0 < s t := Real.rpow_pos_of_pos ht _
  have he : (s t)^10 = t := Real.rpow_inv_natCast_pow ht.le (by norm_num)
  rw [dist_comm, dist_zero_right]
  have hh := stationary_interval_scaled_comparison (hφ a) (hA a) hs htR.le hc hπ hC₀ hC₁ hM₀
    (hzero a) (hcrit a) (hsecond0 a) (hsecond a) (hM a) (hAb a) (hA'b a)
  rw [he] at hh
  exact hh.trans_lt htε

lemma quadratic_phase_third (x : ℝ) : iteratedDeriv 3 (fun x : ℝ => Real.pi*x^2) x = 0 := by
  rw [iteratedDeriv_succ,
    show iteratedDeriv 2 (fun x : ℝ => Real.pi*x^2) = fun _ => 2*Real.pi from funext quadratic_phase_second]
  exact deriv_const x (2*Real.pi)

lemma quadratic_interval_limit {R : ℝ} (hR : 0 < R) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, Complex.exp (I * (Real.pi * t * x^2 : ℝ)))) atTop
      (𝓝 (Complex.exp ((Real.pi : ℂ) / 4 * I))) := by
  let b : ContDiffBump (0 : ℝ) := ⟨R/4, R/2, by positivity, by linarith⟩
  let B : ℝ → ℂ := fun x => (b x : ℂ)
  have hBsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B := by
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR.le⟩
  have hB0 : B 0 = 1 := by
    dsimp [B]
    rw [b.one_of_mem_closedBall (by simp [b]; positivity)]
    exact ofReal_one
  have hBb (x : ℝ) : ‖B x‖ ≤ 1 := by
    simp only [B, norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    exact b.le_one
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hBsm.continuous_deriv (by norm_num)).continuousOn (s := Icc (-R) R)
  have hC₁pos : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0 h0)
  have hQsm : ContDiff ℝ 3 (fun x : ℝ => Real.pi*x^2) := by fun_prop
  have hQ0 : deriv (fun x : ℝ => Real.pi*x^2) 0 = 0 := by rw [quadratic_phase_deriv]; ring
  have hu := stationary_interval_comparison_uniform
    (α := Unit) (φ := fun _ x => Real.pi*x^2) (A := fun _ => B)
    (fun _ => hQsm) (fun _ => hBsm.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) hR
    (c := 2*Real.pi) (by positivity) le_rfl (C₀ := 1) (by norm_num) hC₁pos
    (M := 0) (by norm_num) (fun _ => by simp) (fun _ => hQ0)
    (fun _ => quadratic_phase_second 0)
    (fun _ x _ => by rw [quadratic_phase_second])
    (fun _ x _ => by rw [quadratic_phase_third]; simp)
    (fun _ x _ => hBb x) (fun _ x hx => hC₁ x hx)
  have hdiff := hu.tendsto_at ()
  simp only [hB0, one_mul] at hdiff
  have hsupport : Function.support B ⊆ Ioc (-R) R := by
    intro x hx
    have hbx : x ∈ Function.support (b : ℝ → ℝ) := by
      simpa only [Function.mem_support, B, ofReal_ne_zero] using hx
    rw [b.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hbx
    dsimp [b] at hbx
    exact ⟨by linarith [hbx.1], by linarith [hbx.2]⟩
  have hint (t : ℝ) : (∫ x in -R..R, B x * Complex.exp (I * (Real.pi*t*x^2 : ℝ))) =
      (∫ x : ℝ, B x * Complex.exp (I * (Real.pi*t*x^2 : ℝ))) :=
    intervalIntegral.integral_eq_integral_of_support_subset
      ((Function.support_mul_subset_left _ _).trans hsupport)
  have hbcomp : HasCompactSupport B := b.hasCompactSupport.comp_left ofReal_zero
  have hBlim := quadratic_stationary_compact hbcomp hBsm
  simp only [hB0, mul_one] at hBlim
  simp_rw [← hint] at hBlim
  have he (t x : ℝ) : t*(Real.pi*x^2) = Real.pi*t*x^2 := by ring
  simp only [he] at hdiff
  have hh := hBlim.sub hdiff
  simp only [sub_zero] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  ring

lemma stationary_normalized_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : ∀ a, φ a 0 = 0) (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = 2 * Real.pi)
    (hsecond : ∀ a x, x ∈ Icc (-R) R → c ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))))
      (fun a => A a 0 * Complex.exp ((Real.pi : ℂ) / 4 * I)) atTop := by
  have hu := stationary_interval_comparison_uniform hφ hA hR hc hπ hC₀ hC₁ hM₀
    hzero hcrit hsecond0 hsecond hM hAb hA'b
  have hQ := quadratic_interval_limit hR
  have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR.le⟩
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hε' : 0 < ε / (2 * (C₀ + 1)) := by positivity
  filter_upwards [Metric.tendstoUniformly_iff.mp hu (ε/2) (by positivity),
    (tendsto_def.mp hQ) _ (Metric.ball_mem_nhds _ hε')] with t ht hQt
  intro a
  change dist _ _ < _ at hQt
  rw [dist_eq_norm] at hQt
  have hh := ht a
  rw [dist_comm, dist_zero_right] at hh
  rw [dist_comm, dist_eq_norm]
  have he : (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      A a 0 * Complex.exp ((Real.pi : ℂ)/4*I) =
    (Real.sqrt t : ℂ) * ((∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      A a 0 * (∫ x in -R..R, Complex.exp (I * (Real.pi*t*x^2 : ℝ)))) +
      A a 0 * ((Real.sqrt t : ℂ) * (∫ x in -R..R, Complex.exp (I * (Real.pi*t*x^2 : ℝ))) -
        Complex.exp ((Real.pi : ℂ)/4*I)) := by ring
  rw [he]
  refine (norm_add_le _ _).trans_lt ?_
  have hprod : ‖A a 0 * ((Real.sqrt t : ℂ) *
      (∫ x in -R..R, Complex.exp (I * (Real.pi*t*x^2 : ℝ))) -
        Complex.exp ((Real.pi : ℂ)/4*I))‖ < ε/2 := by
    rw [norm_mul]
    calc
      _ ≤ C₀ * ‖(Real.sqrt t : ℂ) *
        (∫ x in -R..R, Complex.exp (I * (Real.pi*t*x^2 : ℝ))) -
          Complex.exp ((Real.pi : ℂ)/4*I)‖ := mul_le_mul_of_nonneg_right (hAb a 0 h0) (norm_nonneg _)
      _ < (C₀+1) * (ε/(2*(C₀+1))) := by
        exact (mul_le_mul_of_nonneg_right (by linarith : C₀ ≤ C₀+1) (norm_nonneg _)).trans_lt
          (mul_lt_mul_of_pos_left hQt (by positivity))
      _ = ε/2 := by field_simp
  linarith

lemma uniform_rescale {α : Type*} {F : ℝ → α → ℂ} {f b : α → ℂ} {k : α → ℝ}
    (hF : TendstoUniformly F f atTop) {κ C : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C)
    (hk : ∀ a, κ ≤ k a) (hb : ∀ a, ‖b a‖ ≤ C) :
    TendstoUniformly (fun t : ℝ => fun a => b a * F (t*k a) a)
      (fun a => b a * f a) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he : 0 < ε/(C+1) := by positivity
  obtain ⟨T, hT⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hF (ε/(C+1)) he)
  filter_upwards [eventually_ge_atTop (max 0 (T/κ))] with t ht
  intro a
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have htk : T ≤ t*k a := by
    calc
      T = (T/κ)*κ := by field_simp
      _ ≤ t*κ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans ht) hκ.le
      _ ≤ t*k a := mul_le_mul_of_nonneg_left (hk a) ht0
  have h := hT (t*k a) htk a
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  rw [dist_eq_norm] at h
  calc
    _ ≤ (C+1) * ‖f a - F (t*k a) a‖ :=
      mul_le_mul_of_nonneg_right ((hb a).trans (by linarith)) (norm_nonneg _)
    _ < (C+1) * (ε/(C+1)) := mul_lt_mul_of_pos_left h (by positivity)
    _ = ε := by field_simp

lemma stationary_positive_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {k : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c κ C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hκ : 0 < κ) (hk : ∀ a, κ ≤ k a)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : ∀ a, φ a 0 = 0) (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = 2 * Real.pi * k a)
    (hsecond : ∀ a x, x ∈ Icc (-R) R → c*k a ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M*k a)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))))
      (fun a => (Real.sqrt (k a) : ℂ)⁻¹ * (A a 0 * Complex.exp ((Real.pi : ℂ) / 4 * I))) atTop := by
  have hkpos (a : α) : 0 < k a := hκ.trans_le (hk a)
  let ψ : α → ℝ → ℝ := fun a x => (k a)⁻¹ * φ a x
  have hψ (a : α) : ContDiff ℝ 3 (ψ a) := contDiff_const.mul (hφ a)
  have hψ0 (a : α) : ψ a 0 = 0 := by simp [ψ, hzero]
  have hψcrit (a : α) : deriv (ψ a) 0 = 0 := by
    simp only [ψ, deriv_const_mul_field, hcrit, mul_zero]
  have hψsecond0 (a : α) : iteratedDeriv 2 (ψ a) 0 = 2 * Real.pi := by
    simp only [ψ, iteratedDeriv_const_mul_field, hsecond0]
    field_simp [(hkpos a).ne']
  have hψsecond (a : α) (x : ℝ) (hx : x ∈ Icc (-R) R) : c ≤ iteratedDeriv 2 (ψ a) x := by
    dsimp only [ψ]
    rw [iteratedDeriv_const_mul_field, inv_mul_eq_div]
    exact (le_div_iff₀ (hkpos a)).mpr (hsecond a x hx)
  have hψM (a : α) (x : ℝ) (hx : x ∈ Icc (-R) R) : |iteratedDeriv 3 (ψ a) x| ≤ M := by
    dsimp only [ψ]
    rw [iteratedDeriv_const_mul_field, inv_mul_eq_div, abs_div, abs_of_pos (hkpos a)]
    exact (div_le_iff₀ (hkpos a)).mpr (hM a x hx)
  have hu := stationary_normalized_uniform hψ hA hR hc hπ hC₀ hC₁ hM₀
    hψ0 hψcrit hψsecond0 hψsecond hψM hAb hA'b
  have hb (a : α) : ‖(Real.sqrt (k a) : ℂ)⁻¹‖ ≤ (Real.sqrt κ)⁻¹ := by
    rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_anti₀ (Real.sqrt_pos.mpr hκ) (Real.sqrt_le_sqrt (hk a))
  have hv := uniform_rescale hu hκ (by positivity : 0 ≤ (Real.sqrt κ)⁻¹) hk hb
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hv ε hε, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  intro a
  have he (x : ℝ) : (t*k a) * ψ a x = t * φ a x := by
    dsimp [ψ]
    field_simp [(hkpos a).ne']
  have hs : (Real.sqrt (k a) : ℂ)⁻¹ * (Real.sqrt (t*k a) : ℂ) = (Real.sqrt t : ℂ) := by
    rw [Real.sqrt_mul ht0, ofReal_mul]
    field_simp [ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hkpos a)).ne']
  have hh := ht a
  simp_rw [he] at hh
  simpa only [← mul_assoc, hs] using hh

lemma stationary_positive_error_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {k : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c κ C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hκ : 0 < κ) (hk : ∀ a, κ ≤ k a)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = 2 * Real.pi * k a)
    (hsecond : ∀ a x, x ∈ Icc (-R) R → c*k a ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M*k a)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      Complex.exp (I * (t * φ a 0 : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
        (A a 0 * Complex.exp ((Real.pi : ℂ) / 4 * I))))
      (fun _ => 0) atTop := by
  let ψ : α → ℝ → ℝ := fun a x => φ a x - φ a 0
  have hψ (a : α) : ContDiff ℝ 3 (ψ a) := (hφ a).sub contDiff_const
  have hψD (a : α) : deriv (ψ a) 0 = 0 := by
    dsimp only [ψ]; rw [deriv_sub_const, hcrit]
  have hψDD (a : α) (n : ℕ) (hn : 0 < n) (x : ℝ) :
      iteratedDeriv n (ψ a) x = iteratedDeriv n (φ a) x := by
    simpa only [ψ, sub_eq_add_neg, add_comm] using
      (iteratedDeriv_const_add (f := φ a) (x := x) hn (-φ a 0))
  have hu := stationary_positive_uniform hψ hA hR hc hπ hκ hk hC₀ hC₁ hM₀
    (fun a => sub_self _) hψD (by simpa only [hψDD _ 2 (by norm_num)] using hsecond0)
    (by simpa only [hψDD _ 2 (by norm_num)] using hsecond)
    (by simpa only [hψDD _ 3 (by norm_num)] using hM) hAb hA'b
  have hi (a : α) (t : ℝ) :
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) =
      Complex.exp (I * (t * φ a 0 : ℝ)) *
        (∫ x in -R..R, A a x * Complex.exp (I * (t * ψ a x : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [show Complex.exp (I * (t * φ a 0 : ℝ)) *
      (A a x * Complex.exp (I * (t * ψ a x : ℝ))) = A a x *
        (Complex.exp (I * (t * φ a 0 : ℝ)) * Complex.exp (I * (t * ψ a x : ℝ))) by ring,
      ← Complex.exp_add]
    congr 2
    dsimp [ψ]
    push_cast
    ring
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with t ht
  intro a
  rw [dist_comm, dist_zero_right, hi]
  have he : (Real.sqrt t : ℂ) * (Complex.exp (I * (t * φ a 0 : ℝ)) *
        (∫ x in -R..R, A a x * Complex.exp (I * (t * ψ a x : ℝ)))) -
      Complex.exp (I * (t * φ a 0 : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
        (A a 0 * Complex.exp ((Real.pi : ℂ)/4*I))) =
      Complex.exp (I * (t * φ a 0 : ℝ)) * ((Real.sqrt t : ℂ) *
        (∫ x in -R..R, A a x * Complex.exp (I * (t * ψ a x : ℝ))) -
        (Real.sqrt (k a) : ℂ)⁻¹ * (A a 0 * Complex.exp ((Real.pi : ℂ)/4*I))) := by ring
  rw [he, norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [dist_eq_norm, norm_sub_rev] using ht a

lemma nonstationary_scaled_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {l u : α → ℝ} {r C₀ C₁ D : ℝ} (hr : 0 < r) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hlu : ∀ a, l a ≤ u a) (hD : ∀ a, u a - l a ≤ D)
    (hsecond : ∀ a x, x ∈ Icc (l a) (u a) → 0 ≤ iteratedDeriv 2 (φ a) x)
    (hsep : ∀ a x, x ∈ Icc (l a) (u a) → r ≤ |deriv (φ a) x|)
    (hAb : ∀ a x, x ∈ Icc (l a) (u a) → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (l a) (u a) → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in l a..u a, A a x * Complex.exp (I * (t * φ a x : ℝ))))
      (fun _ => 0) atTop := by
  have hbound (a : α) {t : ℝ} (ht : 0 < t) :
      ‖(Real.sqrt t : ℂ) * (∫ x in l a..u a, A a x * Complex.exp (I * (t * φ a x : ℝ)))‖ ≤
        ((4*C₀+D*C₁)/r) / Real.sqrt t := by
    have hq : ContDiff ℝ 2 (deriv (φ a)) := by
      simpa using ((hφ a).of_le (by norm_num : (2 : WithTop ℕ∞)+1 ≤ 3)).deriv'
    have hh := nonstationary_monotone_bound (hlu a) ht.ne' hr hC₀ hC₁
      (φ := φ a) (q := deriv (φ a)) (q' := deriv (deriv (φ a))) (A := A a) (A' := deriv (A a))
      (fun x _ => ((hφ a).differentiable (by norm_num) x).hasDerivAt)
      (fun x _ => (hq.differentiable (by norm_num) x).hasDerivAt)
      (fun x _ => ((hA a).differentiable (by norm_num) x).hasDerivAt)
      (hq.continuous_deriv (by norm_num)).continuousOn
      ((hA a).continuous_deriv (by norm_num)).continuousOn
      (by simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hsecond a)
      (hsep a) (hAb a) (hA'b a)
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
    calc
      _ ≤ Real.sqrt t * ((4*C₀+(u a-l a)*C₁)/(|t| * r)) :=
        mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg t)
      _ ≤ Real.sqrt t * ((4*C₀+D*C₁)/(t*r)) := by
        rw [abs_of_pos ht]
        gcongr
        exact hD a
      _ = _ := by
        have hs := Real.sq_sqrt ht.le
        have hs0 := (Real.sqrt_pos.mpr ht).ne'
        field_simp
        rw [hs]
        ring
  have hlim := Real.tendsto_sqrt_atTop.const_div_atTop ((4*C₀+D*C₁)/r)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with t ht ht0
  intro a
  rw [dist_zero_left]
  exact (hbound a ht0).trans_lt ht

lemma derivative_coercive_center {q : ℝ → ℝ} {l u v c : ℝ}
    (hq : Differentiable ℝ q) (hv : v ∈ Icc l u) (hqv : q v = 0)
    (hc : ∀ x ∈ Icc l u, c ≤ deriv q x) :
    ∀ x ∈ Icc l u, c * |x-v| ≤ |q x| := by
  intro x hx
  have h := (convex_Icc l u).mul_sub_le_image_sub_of_le_deriv
    hq.continuous.continuousOn hq.differentiableOn
    (fun x hx => hc x (interior_subset hx))
  rcases le_total v x with hp | hn
  · have hh := h v hv x hx hp
    rw [hqv, sub_zero] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr hp)]
    exact hh.trans (le_abs_self _)
  · have hh := h x hx v hv hn
    rw [hqv, zero_sub, ← neg_sub x v, mul_neg] at hh
    rw [abs_of_nonpos (sub_nonpos.mpr hn)]
    simpa only [mul_neg] using hh.trans (neg_le_abs _)

lemma stationary_positive_moving_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {k v : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {l u R c κ C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hκ : 0 < κ) (hk : ∀ a, κ ≤ k a)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hv : ∀ a, l+R ≤ v a ∧ v a ≤ u-R)
    (hcrit : ∀ a, deriv (φ a) (v a) = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) (v a) = 2 * Real.pi * k a)
    (hsecond : ∀ a x, x ∈ Icc l u → c*k a ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc l u → |iteratedDeriv 3 (φ a) x| ≤ M*k a)
    (hAb : ∀ a x, x ∈ Icc l u → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc l u → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in l..u, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      Complex.exp (I * (t * φ a (v a) : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
        (A a (v a) * Complex.exp ((Real.pi : ℂ) / 4 * I))))
      (fun _ => 0) atTop := by
  let ψ : α → ℝ → ℝ := fun a x => φ a (x+v a)
  let B : α → ℝ → ℂ := fun a x => A a (x+v a)
  have hψ (a : α) : ContDiff ℝ 3 (ψ a) := (hφ a).comp (contDiff_id.add contDiff_const)
  have hB (a : α) : ContDiff ℝ 2 (B a) := (hA a).comp (contDiff_id.add contDiff_const)
  have hi (a : α) (x : ℝ) (hx : x ∈ Icc (-R) R) : x+v a ∈ Icc l u := by
    constructor <;> have := hv a <;> rcases hx with ⟨hx₁,hx₂⟩ <;> linarith
  have hcenter := stationary_positive_error_uniform hψ hB hR hc hπ hκ hk hC₀ hC₁ hM₀
    (by intro a; simpa only [ψ, deriv_comp_add_const, zero_add] using hcrit a)
    (by intro a; simpa only [ψ, iteratedDeriv_comp_add_const, zero_add] using hsecond0 a)
    (by intro a x hx; simpa only [ψ, iteratedDeriv_comp_add_const] using hsecond a (x+v a) (hi a x hx))
    (by intro a x hx; simpa only [ψ, iteratedDeriv_comp_add_const] using hM a (x+v a) (hi a x hx))
    (by intro a x hx; exact hAb a (x+v a) (hi a x hx))
    (by intro a x hx; simpa only [B, deriv_comp_add_const] using hA'b a (x+v a) (hi a x hx))
  have htt (a : α) (t : ℝ) : (∫ x in -R..R, B a x * Complex.exp (I * (t * ψ a x : ℝ))) =
      ∫ x in v a-R..v a+R, A a x * Complex.exp (I * (t * φ a x : ℝ)) := by
    simpa only [B, ψ, neg_add_eq_sub, add_comm R (v a)] using
      intervalIntegral.integral_comp_add_right (a := -R) (b := R)
        (fun x => A a x * Complex.exp (I * (t * φ a x : ℝ))) (v a)
  simp_rw [htt] at hcenter
  have hpos (a : α) (x : ℝ) (hx : x ∈ Icc l u) : 0 ≤ iteratedDeriv 2 (φ a) x :=
    (mul_pos hc (hκ.trans_le (hk a))).le.trans (hsecond a x hx)
  have hco (a : α) (x : ℝ) (hx : x ∈ Icc l u) : c*κ*|x-v a| ≤ |deriv (φ a) x| := by
    apply derivative_coercive_center
      (((hφ a).deriv' : ContDiff ℝ 2 (deriv (φ a))).differentiable (by norm_num))
      (c := c*κ) (v := v a) (by constructor <;> have := hv a <;> linarith) (hcrit a) _ x hx
    intro y hy
    have := (mul_le_mul_of_nonneg_left (hk a) hc.le).trans (hsecond a y hy)
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using this
  have hleftsub (a : α) : Icc l (v a-R) ⊆ Icc l u :=
    Icc_subset_Icc le_rfl (by have := hv a; linarith)
  have hrightsub (a : α) : Icc (v a+R) u ⊆ Icc l u :=
    Icc_subset_Icc (by have := hv a; linarith) le_rfl
  have hleft := nonstationary_scaled_uniform hφ hA (mul_pos (mul_pos hc hκ) hR) hC₀ hC₁
    (l := fun _ => l) (u := fun a => v a-R) (D := u-l)
    (by intro a; have := hv a; linarith) (by intro a; have := hv a; linarith)
    (fun a x hx => hpos a x (hleftsub a hx))
    (by intro a x hx
        apply le_trans _ (hco a x (hleftsub a hx))
        apply mul_le_mul_of_nonneg_left _ (mul_pos hc hκ).le
        rw [abs_of_nonpos (by rcases hx with ⟨h₁,h₂⟩; linarith)]
        rcases hx with ⟨h₁,h₂⟩; linarith)
    (fun a x hx => hAb a x (hleftsub a hx)) (fun a x hx => hA'b a x (hleftsub a hx))
  have hright := nonstationary_scaled_uniform hφ hA (mul_pos (mul_pos hc hκ) hR) hC₀ hC₁
    (l := fun a => v a+R) (u := fun _ => u) (D := u-l)
    (by intro a; have := hv a; linarith) (by intro a; have := hv a; linarith)
    (fun a x hx => hpos a x (hrightsub a hx))
    (by intro a x hx
        apply le_trans _ (hco a x (hrightsub a hx))
        apply mul_le_mul_of_nonneg_left _ (mul_pos hc hκ).le
        rw [abs_of_nonneg (by rcases hx with ⟨h₁,h₂⟩; linarith)]
        rcases hx with ⟨h₁,h₂⟩; linarith)
    (fun a x hx => hAb a x (hrightsub a hx)) (fun a x hx => hA'b a x (hrightsub a hx))
  convert (hleft.add hcenter).add hright using 1
  · ext t a
    dsimp only [Pi.add_apply, B, ψ, zero_add]
    have hF : Continuous (fun x => A a x * Complex.exp (I * (t * φ a x : ℝ))) := by fun_prop
    have hs := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) (a := l) (b := v a-R))
      (hF.intervalIntegrable (μ := volume) (a := v a-R) (b := v a+R))
    have hs' := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) (a := l) (b := v a+R))
      (hF.intervalIntegrable (μ := volume) (a := v a+R) (b := u))
    rw [← hs', ← hs]
    ring_nf
  · ext a; simp

/-- Uniform stationary phase with ordinary lower and upper curvature bounds. -/
lemma stationary_positive_moving_of_bounds {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {v : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {l u R d D C₀ C₁ M : ℝ} (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hv : ∀ a, l+R ≤ v a ∧ v a ≤ u-R)
    (hcrit : ∀ a, deriv (φ a) (v a) = 0)
    (hsecond : ∀ a x, x ∈ Icc l u → d ≤ iteratedDeriv 2 (φ a) x)
    (hupper : ∀ a x, x ∈ Icc l u → iteratedDeriv 2 (φ a) x ≤ D)
    (hM : ∀ a x, x ∈ Icc l u → |iteratedDeriv 3 (φ a) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc l u → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc l u → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in l..u, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      Complex.exp (I * (t * φ a (v a) : ℝ)) *
        ((Real.sqrt (iteratedDeriv 2 (φ a) (v a) / (2*Real.pi)) : ℂ)⁻¹ *
          (A a (v a) * Complex.exp ((Real.pi : ℂ) / 4 * I))))
      (fun _ => 0) atTop := by
  have hπ : 0 < 2*Real.pi := by positivity
  have hD : 0 < D := hd.trans_le hdD
  have hv' (a : α) : v a ∈ Icc l u := by
    constructor <;> have := hv a <;> linarith
  let k : α → ℝ := fun a => iteratedDeriv 2 (φ a) (v a)/(2*Real.pi)
  have hk (a : α) : d/(2*Real.pi) ≤ k a :=
    div_le_div_of_nonneg_right (hsecond a (v a) (hv' a)) hπ.le
  have hk' (a : α) : k a ≤ D/(2*Real.pi) :=
    div_le_div_of_nonneg_right (hupper a (v a) (hv' a)) hπ.le
  refine stationary_positive_moving_uniform hφ hA hR (c := d*(2*Real.pi)/D)
    (div_pos (mul_pos hd hπ) hD) ?_ (div_pos hd hπ) hk hC₀ hC₁
    (M := M/(d/(2*Real.pi))) (div_nonneg hM₀ (div_pos hd hπ).le) hv hcrit ?_ ?_ ?_ hAb hA'b
  · exact (div_le_iff₀ hD).mpr (by nlinarith)
  · intro a
    field_simp
  · intro a x hx
    calc
      d*(2*Real.pi)/D*k a ≤ d*(2*Real.pi)/D*(D/(2*Real.pi)) :=
        mul_le_mul_of_nonneg_left (hk' a) (by positivity)
      _ = d := by field_simp
      _ ≤ _ := hsecond a x hx
  · intro a x hx
    apply (hM a x hx).trans
    calc
      M = (M/(d/(2*Real.pi)))*(d/(2*Real.pi)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hk a) (by positivity)

lemma deriv_sub_linear_phase {Φ : ℝ → ℝ} (hΦ : Differentiable ℝ Φ) (s x : ℝ) :
    deriv (fun x => Φ x-s*x) x = deriv Φ x-s := by
  rw [deriv_fun_sub (f := Φ) (g := fun x => s*x) (hΦ x) (by fun_prop)]
  simp

lemma iteratedDeriv_sub_linear_phase {Φ : ℝ → ℝ} {n : ℕ}
    (hΦ : ContDiff ℝ n Φ) (hn : 2 ≤ n) (s x : ℝ) :
    iteratedDeriv n (fun x => Φ x-s*x) x = iteratedDeriv n Φ x := by
  rw [iteratedDeriv_fun_sub (f := Φ) (g := fun x => s*x) hΦ.contDiffAt (by fun_prop)]
  have hl : iteratedDeriv n (fun x : ℝ => s*x) x = 0 := by
    calc
      _ = s * iteratedDeriv n (id : ℝ → ℝ) x := iteratedDeriv_const_mul_field s id
      _ = 0 := by simp [iteratedDeriv_id, show n ≠ 0 by omega, show n ≠ 1 by omega]
  rw [hl, sub_zero]

lemma stationary_branch_center {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    {a b : ℝ} (hab : a ≤ b) {s : ℝ} (hs : s ∈ Icc (deriv Φ a) (deriv Φ b)) :
    Function.invFunOn (deriv Φ) (Icc a b) s ∈ Icc a b ∧
      deriv Φ (Function.invFunOn (deriv Φ) (Icc a b) s) = s := by
  have hh := intermediate_value_Icc hab (hΦ.continuous_deriv (by norm_num)).continuousOn hs
  exact Function.invFunOn_pos hh

lemma intervalIntegral_phase_of_support {A : ℝ → ℂ} {a b : ℝ}
    (hA : Function.support A ⊆ Ioc a b) (Φ : ℝ → ℝ) (t : ℝ) :
    (∫ x in a..b, A x * Complex.exp (I * (t*Φ x : ℝ))) =
      ∫ x, A x * Complex.exp (I * (t*Φ x : ℝ)) := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  apply hA
  exact (mul_ne_zero_iff.mp hx).1

lemma phase_nonstationary_off_branch {α : Type*} {Φ : ℝ → ℝ} {A : α → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {a b R d C₀ C₁ : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) :
    TendstoUniformly (fun t : ℝ => fun p : α ×
      {s : ℝ // s ∉ Icc (deriv Φ (a-R)) (deriv Φ (b+R))} =>
      (Real.sqrt t : ℂ) * (∫ x, A p.1 x * Complex.exp (I * (t*(Φ x-p.2.val*x) : ℝ))))
        (fun _ => 0) atTop := by
  let β := α × {s : ℝ // s ∉ Icc (deriv Φ (a-R)) (deriv Φ (b+R))}
  let φ : β → ℝ → ℝ := fun p x => Φ x-p.2.val*x
  let B : β → ℝ → ℂ := fun p => A p.1
  have hφ (p : β) : ContDiff ℝ 3 (φ p) := hΦ.sub (contDiff_const.mul contDiff_id)
  have hB (p : β) : ContDiff ℝ 2 (B p) := hA p.1
  have hi : Icc a b ⊆ Icc (a-2*R) (b+2*R) := by
    apply Icc_subset_Icc <;> linarith
  have hq : Differentiable ℝ (deriv Φ) :=
    (hΦ.deriv' : ContDiff ℝ 2 (deriv Φ)).differentiable (by norm_num)
  have hmv := (convex_Icc (a-2*R) (b+2*R)).mul_sub_le_image_sub_of_le_deriv
    hq.continuous.continuousOn hq.differentiableOn
    (fun x hx => show d ≤ deriv (deriv Φ) x from by
      simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
        hsecond x (interior_subset hx))
  have hlo : a-R ∈ Icc (a-2*R) (b+2*R) := by constructor <;> linarith
  have hhi : b+R ∈ Icc (a-2*R) (b+2*R) := by constructor <;> linarith
  have hsep (p : β) (x : ℝ) (hx : x ∈ Icc a b) : d*R ≤ |deriv (φ p) x| := by
    rw [deriv_sub_linear_phase (hΦ.differentiable (by norm_num))]
    have hp := p.2.property
    simp only [mem_Icc, not_and_or, not_le] at hp
    rcases hp with hp | hp
    · have hm := hmv (a-R) hlo x (hi hx) (by rcases hx with ⟨h₁,h₂⟩; linarith)
      have hd' : d*R ≤ deriv Φ x-p.2.val := by
        have hxx : R ≤ x-(a-R) := by rcases hx with ⟨h₁,h₂⟩; linarith
        have := mul_le_mul_of_nonneg_left hxx hd.le
        linarith
      exact hd'.trans (le_abs_self _)
    · have hm := hmv x (hi hx) (b+R) hhi (by rcases hx with ⟨h₁,h₂⟩; linarith)
      have hd' : d*R ≤ -(deriv Φ x-p.2.val) := by
        have hxx : R ≤ b+R-x := by rcases hx with ⟨h₁,h₂⟩; linarith
        have := mul_le_mul_of_nonneg_left hxx hd.le
        linarith
      exact hd'.trans (neg_le_abs _)
  have hu := nonstationary_scaled_uniform hφ hB (mul_pos hd hR) hC₀ hC₁
    (l := fun _ => a) (u := fun _ => b) (D := b-a)
    (fun _ => hab) (fun _ => le_rfl)
    (by intro p x hx
        rw [iteratedDeriv_sub_linear_phase (hΦ.of_le (by norm_num)) (by norm_num)]
        exact hd.le.trans (hsecond x (hi hx))) hsep
    (fun p x hx => hAb p.1 x (hi hx)) (fun p x hx => hA'b p.1 x (hi hx))
  convert hu using 1
  all_goals try with_reducible_and_instances rfl
  ext t p
  rw [intervalIntegral_phase_of_support (hsupp p.1)]

lemma phase_stationary_on_branch {α : Type*} {Φ : ℝ → ℝ} {A : α → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {a b R d D C₀ C₁ M : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ D)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) :
    TendstoUniformly (fun t : ℝ => fun p : α ×
      {s : ℝ // s ∈ Icc (deriv Φ (a-R)) (deriv Φ (b+R))} =>
      (Real.sqrt t : ℂ) * (∫ x, A p.1 x * Complex.exp (I * (t*(Φ x-p.2.val*x) : ℝ))) -
        stationaryLeading Φ (A p.1) (a-R) (b+R) p.2.val t)
        (fun _ => 0) atTop := by
  let β := α × {s : ℝ // s ∈ Icc (deriv Φ (a-R)) (deriv Φ (b+R))}
  let φ : β → ℝ → ℝ := fun p x => Φ x-p.2.val*x
  let B : β → ℝ → ℂ := fun p => A p.1
  let v : β → ℝ := fun p => Function.invFunOn (deriv Φ) (Icc (a-R) (b+R)) p.2.val
  have hv (p : β) : v p ∈ Icc (a-R) (b+R) ∧ deriv Φ (v p) = p.2.val :=
    stationary_branch_center (hΦ.of_le (by norm_num)) (by linarith) p.2.property
  have hφ (p : β) : ContDiff ℝ 3 (φ p) := hΦ.sub (contDiff_const.mul contDiff_id)
  have hB (p : β) : ContDiff ℝ 2 (B p) := hA p.1
  have h2 (p : β) (x : ℝ) : iteratedDeriv 2 (φ p) x = iteratedDeriv 2 Φ x :=
    iteratedDeriv_sub_linear_phase (hΦ.of_le (by norm_num)) (by norm_num) p.2.val x
  have h3 (p : β) (x : ℝ) : iteratedDeriv 3 (φ p) x = iteratedDeriv 3 Φ x :=
    iteratedDeriv_sub_linear_phase hΦ (by norm_num) p.2.val x
  have hu := stationary_positive_moving_of_bounds hφ hB hR hd hdD hC₀ hC₁ hM₀
    (l := a-2*R) (u := b+2*R) (v := v)
    (by intro p; constructor <;> have := (hv p).1 <;> rcases this with ⟨h₁,h₂⟩ <;> linarith)
    (by intro p; rw [deriv_sub_linear_phase (hΦ.differentiable (by norm_num)), (hv p).2, sub_self])
    (by intro p x hx; rw [h2]; exact hsecond x hx)
    (by intro p x hx; rw [h2]; exact hupper x hx)
    (by intro p x hx; rw [h3]; exact hM x hx)
    (fun p x hx => hAb p.1 x hx) (fun p x hx => hA'b p.1 x hx)
  have hs (p : β) : Function.support (B p) ⊆ Ioc (a-2*R) (b+2*R) := by
    intro x hx
    have hh := hsupp p.1 hx
    constructor <;> rcases hh with ⟨h₁,h₂⟩ <;> linarith
  simp_rw [intervalIntegral_phase_of_support (hs _), h2] at hu
  convert hu using 1
  all_goals try with_reducible_and_instances rfl
  ext t p
  simp only [stationaryLeading, ite_eq_left p.2.property]
  rfl

/-- Compactly supported, parameter-uniform stationary phase, including the
noncritical region and zero amplitudes. No weak-convergence replacement is used. -/
lemma compact_support_stationary_uniform {α : Type*} {Φ : ℝ → ℝ} {A : α → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {a b R d D C₀ C₁ M : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ D)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) :
    TendstoUniformly (fun t : ℝ => fun p : α × ℝ =>
      (Real.sqrt t : ℂ) * (∫ x, A p.1 x * Complex.exp (I * (t*(Φ x-p.2*x) : ℝ))) -
        stationaryLeading Φ (A p.1) (a-R) (b+R) p.2 t)
        (fun _ => 0) atTop := by
  have hin := phase_stationary_on_branch hΦ hA hab hR hd hdD hC₀ hC₁ hM₀
    hsecond hupper hM hAb hA'b hsupp
  have hout := phase_nonstationary_off_branch hΦ hA hab hR hd hC₀ hC₁ hsecond hAb hA'b hsupp
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hin ε hε,
    Metric.tendstoUniformly_iff.mp hout ε hε] with t ht₁ ht₂
  intro p
  by_cases hp : p.2 ∈ Icc (deriv Φ (a-R)) (deriv Φ (b+R))
  · exact ht₁ (p.1, ⟨p.2,hp⟩)
  · simpa only [stationaryLeading, ite_eq_right hp, sub_zero] using ht₂ (p.1, ⟨p.2,hp⟩)

lemma norm_stationaryLeading {Φ : ℝ → ℝ} {A : ℝ → ℂ} {l u s t : ℝ}
    (hs : s ∈ Icc (deriv Φ l) (deriv Φ u)) :
    ‖stationaryLeading Φ A l u s t‖ =
      (Real.sqrt (iteratedDeriv 2 Φ (Function.invFunOn (deriv Φ) (Icc l u) s) /
        (2*Real.pi)))⁻¹ * ‖A (Function.invFunOn (deriv Φ) (Icc l u) s)‖ := by
  simp only [stationaryLeading, ite_eq_left hs, norm_mul, norm_inv]
  simp [Complex.norm_exp, mul_re, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma stationaryLeading_bound {Φ : ℝ → ℝ} {A : ℝ → ℂ} {l u s t d C : ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (hlu : l ≤ u) (hd : 0 < d) (hC : 0 ≤ C)
    (hsecond : ∀ x ∈ Icc l u, d ≤ iteratedDeriv 2 Φ x)
    (hA : ∀ x ∈ Icc l u, ‖A x‖ ≤ C) :
    ‖stationaryLeading Φ A l u s t‖ ≤ C / Real.sqrt (d/(2*Real.pi)) := by
  by_cases hs : s ∈ Icc (deriv Φ l) (deriv Φ u)
  · rw [norm_stationaryLeading hs]
    have hv := (stationary_branch_center hΦ hlu hs).1
    have hd' : 0 < d/(2*Real.pi) := by positivity
    have hroot : Real.sqrt (d/(2*Real.pi)) ≤
        Real.sqrt (iteratedDeriv 2 Φ (Function.invFunOn (deriv Φ) (Icc l u) s)/(2*Real.pi)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (hsecond _ hv) (by positivity))
    calc
      _ ≤ (Real.sqrt (iteratedDeriv 2 Φ (Function.invFunOn (deriv Φ) (Icc l u) s)/(2*Real.pi)))⁻¹ * C :=
        mul_le_mul_of_nonneg_left (hA _ hv) (by positivity)
      _ ≤ (Real.sqrt (d/(2*Real.pi)))⁻¹ * C := mul_le_mul_of_nonneg_right
        (by simpa only [one_div] using one_div_le_one_div_of_le (Real.sqrt_pos.mpr hd') hroot) hC
      _ = _ := by ring
  · simp only [stationaryLeading, ite_eq_right hs, norm_zero]
    positivity

lemma compact_phase_tail_bound {Φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ContDiff ℝ 2 A)
    {a b t s M C₀ C₁ : ℝ} (hab : a ≤ b) (ht : 0 < t) (hs : s ≠ 0)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsM : 2*M ≤ |s|)
    (hfirst : ∀ x ∈ Icc a b, |deriv Φ x| ≤ M)
    (hsecond : ∀ x ∈ Icc a b, 0 ≤ iteratedDeriv 2 Φ x)
    (hAb : ∀ x ∈ Icc a b, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc a b, ‖deriv A x‖ ≤ C₁)
    (hsupp : Function.support A ⊆ Ioc a b) :
    ‖∫ x, A x * Complex.exp (I * (t*(Φ x-s*x) : ℝ))‖ ≤
      2*(4*C₀+(b-a)*C₁)/(t*|s|) := by
  let φ : ℝ → ℝ := fun x => Φ x-s*x
  have hφ : ContDiff ℝ 3 φ := hΦ.sub (contDiff_const.mul contDiff_id)
  have hq : ContDiff ℝ 2 (deriv φ) := hφ.deriv'
  have hsep (x : ℝ) (hx : x ∈ Icc a b) : |s|/2 ≤ |deriv φ x| := by
    rw [deriv_sub_linear_phase (hΦ.differentiable (by norm_num))]
    have htri : |s| ≤ |deriv Φ x-s|+|deriv Φ x| := by
      calc
        _ = |deriv Φ x-(deriv Φ x-s)| := by congr 1; ring
        _ ≤ |deriv Φ x|+|deriv Φ x-s| := by simpa only [Real.norm_eq_abs] using norm_sub_le (deriv Φ x) (deriv Φ x-s)
        _ = _ := by ring
    have hh := hfirst x hx
    linarith
  have hh := nonstationary_monotone_bound hab ht.ne' (half_pos (abs_pos.mpr hs)) hC₀ hC₁
    (φ := φ) (q := deriv φ) (q' := deriv (deriv φ)) (A := A) (A' := deriv A)
    (fun x _ => (hφ.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hq.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hA.differentiable (by norm_num) x).hasDerivAt)
    (hq.continuous_deriv (by norm_num)).continuousOn
    (hA.continuous_deriv (by norm_num)).continuousOn
    (by intro x hx
        have hh := hsecond x hx
        have he := iteratedDeriv_sub_linear_phase (hΦ.of_le (by norm_num)) (by norm_num : 2 ≤ 2) s x
        simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hh.trans he.ge)
    hsep hAb hA'b
  rw [intervalIntegral_phase_of_support hsupp] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_of_pos ht]
  field_simp

end ThreeTorus
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology
namespace ThreeTorus

lemma norm_sq_difference_bound (z w : ℂ) {ε L : ℝ} (hε : 0 ≤ ε) (_hL : 0 ≤ L)
    (he : ‖z-w‖ ≤ ε) (hw : ‖w‖ ≤ L) :
    |‖z‖^2-‖w‖^2| ≤ ε*(ε+2*L) := by
  have hz : ‖z‖ ≤ ε+L := by
    calc
      ‖z‖ ≤ ‖z-w‖+‖w‖ := by simpa [norm_sub_rev, add_comm] using norm_le_insert w z
      _ ≤ _ := add_le_add he hw
  calc
    _ = |‖z‖-‖w‖| *(‖z‖+‖w‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖z‖+‖w‖)]
      ring
    _ ≤ ε*(ε+2*L) := mul_le_mul ((abs_norm_sub_norm_le z w).trans he)
      (by linarith) (by positivity) hε

lemma stationary_pointwise_mass_bound (z w : ℂ) {N ε L : ℝ} (hN : 0 < N)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (he : ‖(Real.sqrt N : ℂ)*z-w‖ ≤ ε) (hw : ‖w‖ ≤ L) :
    |‖z‖^2-N⁻¹*‖w‖^2| ≤ (ε*(ε+2*L))/N := by
  have h := norm_sq_difference_bound ((Real.sqrt N : ℂ)*z) w hε hL he hw
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hN.le] at h
  apply (le_div_iff₀ hN).mpr
  calc
    _ = |N*‖z‖^2-‖w‖^2| := by
      calc
        _ = |(‖z‖^2-N⁻¹*‖w‖^2)*N| := by rw [abs_mul, abs_of_pos hN]
        _ = _ := by congr 1; field_simp
    _ ≤ _ := h

lemma stationary_integrated_mass_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C Ld : Ω → ℂ} {N ε L : ℝ}
    (hN : 0 < N) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hi : Integrable (fun x => |‖C x‖^2-N⁻¹*‖Ld x‖^2|) μ)
    (he : ∀ x, ‖(Real.sqrt N : ℂ)*C x-Ld x‖ ≤ ε) (hw : ∀ x, ‖Ld x‖ ≤ L) :
    (∫ x, |‖C x‖^2-N⁻¹*‖Ld x‖^2| ∂μ) ≤ ε*(ε+2*L)/N := by
  calc
    _ ≤ ∫ _ : Ω, ε*(ε+2*L)/N ∂μ := integral_mono hi (integrable_const _)
      (fun x => stationary_pointwise_mass_bound (C x) (Ld x) hN hε hL (he x) (hw x))
    _ = _ := by simp

lemma integer_band_card_bound (K n : ℕ) (hn : 1 ≤ n) :
    ((Finset.Icc (-(K*n : ℤ)) (K*n)).card : ℝ) ≤ (2*(K:ℝ)+1)*(n:ℝ) := by
  rw [Int.card_Icc]
  have he : ((K*n : ℤ)+1-(-(K*n : ℤ))).toNat = 2*K*n+1 := by
    have he' : (K*n : ℤ)+1-(-(K*n : ℤ)) = ((2*K*n+1 : ℕ) : ℤ) := by push_cast; ring
    rw [he']
    exact Int.toNat_natCast _
  rw [he]
  push_cast
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

lemma stationary_band_mass_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C Ld : ℤ → Ω → ℂ} {ε L : ℝ}
    (K n : ℕ) (hn : 1 ≤ n) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hi : ∀ j, Integrable (fun x => |‖C j x‖^2-(n:ℝ)⁻¹*‖Ld j x‖^2|) μ)
    (he : ∀ j x, ‖(Real.sqrt n : ℂ)*C j x-Ld j x‖ ≤ ε)
    (hw : ∀ j x, ‖Ld j x‖ ≤ L) :
    (∑ j ∈ Finset.Icc (-(K*n : ℤ)) (K*n), ∫ x, |‖C j x‖^2-(n:ℝ)⁻¹*‖Ld j x‖^2| ∂μ)
      ≤ (2*(K:ℝ)+1)*(ε*(ε+2*L)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc
    _ ≤ ∑ j ∈ Finset.Icc (-(K*n : ℤ)) (K*n), ε*(ε+2*L)/(n:ℝ) :=
      Finset.sum_le_sum (fun j _ => stationary_integrated_mass_bound hn' hε hL (hi j) (he j) (hw j))
    _ = ((Finset.Icc (-(K*n : ℤ)) (K*n)).card : ℝ)*(ε*(ε+2*L)/(n:ℝ)) := by simp
    _ ≤ ((2*(K:ℝ)+1)*(n:ℝ))*(ε*(ε+2*L)/(n:ℝ)) :=
      mul_le_mul_of_nonneg_right (integer_band_card_bound K n hn) (by positivity)
    _ = _ := by field_simp

lemma integer_band_exhausts (K : ℕ) (hK : 1 ≤ K) (j : ℤ) :
    ∀ᶠ n : ℕ in atTop, j ∈ Finset.Icc (-(K*n : ℤ)) (K*n) := by
  filter_upwards [eventually_ge_atTop j.natAbs] with n hn
  have hab : |j| ≤ (n : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hn
  have hkn : (n : ℤ) ≤ (K : ℤ)*n := by
    have hKn : n ≤ K*n := by nlinarith
    exact_mod_cast hKn
  simpa only [Finset.mem_Icc] using abs_le.mp (hab.trans hkn)

lemma stationary_tail_mass_tendsto {E : ℕ → ℤ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    {B : ℤ → ℝ} (hB : Summable B)
    (hE0 : ∀ n j, 0 ≤ E n j)
    (hEB : ∀ᶠ n : ℕ in atTop, ∀ j, j ∉ Finset.Icc (-(K*n : ℤ)) (K*n) → E n j ≤ B j) :
    Tendsto (fun n : ℕ => ∑' j : ℤ,
      if j ∈ Finset.Icc (-(K*n : ℤ)) (K*n) then 0 else E n j) atTop (𝓝 0) := by
  classical
  have hB' : Summable (fun j => |B j|) := hB.abs
  have hh := tendsto_tsum_of_dominated_convergence (bound := fun j => |B j|) hB'
    (f := fun n : ℕ => fun j : ℤ => if j ∈ Finset.Icc (-(K*n : ℤ)) (K*n) then 0 else E n j)
    (g := fun _ : ℤ => (0 : ℝ))
    (fun j => tendsto_const_nhds.congr' (by
      filter_upwards [integer_band_exhausts K hK j] with n hn
      simp only [ite_eq_left hn]))
    (by filter_upwards [hEB] with n hn
        intro j
        split_ifs with hj
        · simp only [norm_zero]; exact abs_nonneg _
        · rw [Real.norm_eq_abs, abs_of_nonneg (hE0 n j)]
          exact (hn j hj).trans (le_abs_self _))
  simpa only [tsum_zero] using hh

lemma stationary_tail_square_bound_summable (D : ℝ) :
    Summable (fun j : ℤ => D^2/(j:ℝ)^2) := by
  simpa only [mul_one_div] using
    ((Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left (D^2))

lemma stationary_band_mass_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C Ld : ℕ → ℤ → Ω → ℂ} {L : ℝ}
    (K : ℕ) (hL : 0 ≤ L)
    (hi : ∀ n j, Integrable (fun x => |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2|) μ)
    (he : TendstoUniformly (fun n : ℕ => fun p : ℤ × Ω =>
      (Real.sqrt n : ℂ)*C n p.1 p.2-Ld n p.1 p.2) (fun _ => 0) atTop)
    (hw : ∀ n j x, ‖Ld n j x‖ ≤ L) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(K*n : ℤ)) (K*n),
      ∫ x, |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2| ∂μ) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let c : ℝ := 2*(K:ℝ)+1
  have hc : 0 < c := by dsimp [c]; positivity
  let δ : ℝ := min 1 (ε/(2*c*(1+2*L)))
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε/(2*c*(1+2*L)) := min_le_right _ _
  have hbound : c*(δ*(δ+2*L)) < ε := by
    calc
      _ ≤ c*(δ*(1+2*L)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith : δ+2*L ≤ 1+2*L) hδ.le) hc.le
      _ ≤ c*((ε/(2*c*(1+2*L)))*(1+2*L)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hδ2 (by positivity)) hc.le
      _ = ε/2 := by field_simp
      _ < ε := by linarith
  filter_upwards [Metric.tendstoUniformly_iff.mp he δ hδ,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hb := stationary_band_mass_bound K n hn1 hδ.le hL (hi n)
    (fun j x => by simpa only [dist_zero_left] using (hn (j,x)).le) (hw n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  exact hb.trans_lt hbound

lemma tsum_band_tail_decomposition {E B : ℤ → ℝ} (S : Finset ℤ)
    (hE : ∀ j, 0 ≤ E j) (hB : Summable B) (hEB : ∀ j ∉ S, E j ≤ B j) :
    (∑' j, E j) = (∑ j ∈ S, E j) + ∑' j, if j ∈ S then 0 else E j := by
  classical
  have hs : HasSum (fun j => if j ∈ S then E j else 0) (∑ j ∈ S, E j) := by
    convert hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ) (s := S)
      (fun j hj => show (if j ∈ S then E j else 0) = 0 by simp [hj]) using 1
    all_goals try with_reducible_and_instances rfl
    exact Finset.sum_congr rfl (fun j hj => by simp [hj])
  have ht : Summable (fun j => if j ∈ S then 0 else E j) := by
    apply hB.abs.of_norm_bounded
    intro j
    split_ifs with hj
    · simp
    · rw [Real.norm_eq_abs, abs_of_nonneg (hE j)]
      exact (hEB j hj).trans (le_abs_self _)
  have hh := hs.add ht.hasSum
  have he (j : ℤ) : (if j ∈ S then E j else 0) + (if j ∈ S then 0 else E j) = E j := by
    split_ifs <;> simp
  exact (hh.congr_fun (fun j => (he j).symm)).tsum_eq

lemma tsum_tendsto_zero_of_band_and_tail {E : ℕ → ℤ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    {B : ℤ → ℝ} (hB : Summable B) (hE0 : ∀ n j, 0 ≤ E n j)
    (hEB : ∀ᶠ n : ℕ in atTop, ∀ j, j ∉ Finset.Icc (-(K*n : ℤ)) (K*n) → E n j ≤ B j)
    (hc : Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(K*n : ℤ)) (K*n), E n j) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, E n j) atTop (𝓝 0) := by
  have ht := stationary_tail_mass_tendsto hK hB hE0 hEB
  have hh := hc.add ht
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hEB] with n hn
  exact (tsum_band_tail_decomposition _ (hE0 n) hB hn).symm

/-- Summed L¹ coefficient-mass conclusion; unlike weak convergence this controls
all retained index subarrays and their pushforwards. -/
lemma summed_stationary_mass {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C Ld : ℕ → ℤ → Ω → ℂ} {L D : ℝ}
    (K : ℕ) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (hi : ∀ n j, Integrable (fun x => |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2|) μ)
    (he : TendstoUniformly (fun n : ℕ => fun p : ℤ × Ω =>
      (Real.sqrt n : ℂ)*C n p.1 p.2-Ld n p.1 p.2) (fun _ => 0) atTop)
    (hw : ∀ n j x, ‖Ld n j x‖ ≤ L)
    (ht : ∀ᶠ n : ℕ in atTop, ∀ j, j ∉ Finset.Icc (-(K*n : ℤ)) (K*n) →
      (∫ x, |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2| ∂μ) ≤ D^2/(j:ℝ)^2) :
    Tendsto (fun n : ℕ => ∑' j : ℤ,
      ∫ x, |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2| ∂μ) atTop (𝓝 0) := by
  exact tsum_tendsto_zero_of_band_and_tail hK (stationary_tail_square_bound_summable D)
    (by intros; positivity) ht (stationary_band_mass_tendsto K hL hi he hw)

end ThreeTorus

namespace ThreeTorus

lemma passage_uniform_error {Ω : Type*} {Φ : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ z, ContDiff ℝ 2 (A z))
    {a b R d D C₀ C₁ M : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ D)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) (κ : ℝ) (α : ℕ → ℝ) :
    TendstoUniformly (fun n : ℕ => fun p : ℤ × Ω =>
      (Real.sqrt n : ℂ)*passageCoefficient Φ A κ α n p.1 p.2 -
        passageLeading Φ A a b R κ α n p.1 p.2) (fun _ => 0) atTop := by
  have hh := compact_support_stationary_uniform hΦ hA hab hR hd hdD hC₀ hC₁ hM₀
    hsecond hupper hM hAb hA'b hsupp
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ))
    (Metric.tendstoUniformly_iff.mp hh ε hε)] with n hn
  intro p
  exact hn (p.2, passageSlope κ α n p.1)

lemma passageSlope_large {κ C M : ℝ} {α : ℕ → ℝ} {K n : ℕ} {j : ℤ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 2*(C+M+1) ≤ κ*K)
    (hn : 1 ≤ n) (hα : |α n| ≤ C) (hj : j ∉ Finset.Icc (-(K*n : ℤ)) (K*n)) :
    2*M < |passageSlope κ α n j| ∧
      κ*|(j:ℝ)|/(2*(n:ℝ)) ≤ |passageSlope κ α n j| ∧ j ≠ 0 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hj' : (K:ℝ)*n < |(j:ℝ)| := by
    have hji : (K:ℤ)*n < |j| := by
      simpa only [Finset.mem_Icc, ← abs_le, not_le] using hj
    exact_mod_cast hji
  have hv : κ*K < κ*|(j:ℝ)|/(n:ℝ) := by
    apply (lt_div_iff₀ hn').mpr
    nlinarith
  have htri : κ*|(j:ℝ)|/(n:ℝ)-C ≤ |passageSlope κ α n j| := by
    have ht := abs_sub_abs_le_abs_sub (κ*(j:ℝ)/(n:ℝ)) (α n)
    rw [abs_div, abs_mul, abs_of_pos hκ, abs_of_pos hn'] at ht
    dsimp [passageSlope]
    linarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [show κ*|(j:ℝ)|/(2*(n:ℝ)) = (κ*|(j:ℝ)|/(n:ℝ))/2 by ring]
    linarith
  · intro he
    subst j
    simp only [Int.cast_zero, abs_zero] at hj'
    have : 0 ≤ (K:ℝ)*n := by positivity
    linarith

lemma passage_arrays_tail {Ω : Type*} {Φ : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ z, ContDiff ℝ 2 (A z))
    {a b R d C₀ C₁ M C κ : ℝ} {α : ℕ → ℝ} {K n : ℕ} {j : ℤ}
    (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hκ : 0 < κ) (hK : 2*(C+M+1) ≤ κ*K)
    (hn : 1 ≤ n) (hα : |α n| ≤ C)
    (hfirst : ∀ x ∈ Icc (a-2*R) (b+2*R), |deriv Φ x| ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b)
    (hj : j ∉ Finset.Icc (-(K*n:ℤ)) (K*n)) (z : Ω) :
    passageLeading Φ A a b R κ α n j z = 0 ∧
      ‖passageCoefficient Φ A κ α n j z‖ ≤ (4*(4*C₀+(b-a)*C₁)/κ)/|(j:ℝ)| := by
  obtain ⟨hlarge,hlower,hj0⟩ := passageSlope_large hκ hC hM hK hn hα hj
  have hn' : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsub : Icc a b ⊆ Icc (a-2*R) (b+2*R) := by intro x hx; constructor <;> linarith [hx.1,hx.2]
  have hleft : a-R ∈ Icc (a-2*R) (b+2*R) := by constructor <;> linarith
  have hright : b+R ∈ Icc (a-2*R) (b+2*R) := by constructor <;> linarith
  have hnot : passageSlope κ α n j ∉ Icc (deriv Φ (a-R)) (deriv Φ (b+R)) := by
    intro hh
    have hl := abs_le.mp (hfirst _ hleft)
    have hr := abs_le.mp (hfirst _ hright)
    have hh' : |passageSlope κ α n j| ≤ M := abs_le.mpr ⟨hl.1.trans hh.1,hh.2.trans hr.2⟩
    linarith
  refine ⟨by simp only [passageLeading, stationaryLeading, ite_eq_right hnot], ?_⟩
  have hs : passageSlope κ α n j ≠ 0 := abs_pos.mp (lt_of_le_of_lt (by positivity : 0 ≤ 2*M) hlarge)
  have hb := compact_phase_tail_bound hΦ (hA z) hab hn' hs hC₀ hC₁ hlarge.le
    (fun x hx => hfirst x (hsub hx)) (fun x hx => hd.le.trans (hsecond x (hsub hx)))
    (fun x hx => hAb z x (hsub hx)) (fun x hx => hA'b z x (hsub hx)) (hsupp z)
  apply hb.trans
  have hjpos : 0 < |(j:ℝ)| := abs_pos.mpr (by exact_mod_cast hj0)
  have hnum : 0 ≤ 2*(4*C₀+(b-a)*C₁) := by positivity
  calc
    _ ≤ (2*(4*C₀+(b-a)*C₁))/((n:ℝ)*(κ*|(j:ℝ)|/(2*(n:ℝ)))) :=
      div_le_div_of_nonneg_left hnum (by positivity) (mul_le_mul_of_nonneg_left hlower hn'.le)
    _ = _ := by field_simp; ring

/-- The strong summed mass estimate used in the passage lemma. -/
lemma passage_summed_mass {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Φ : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ z, ContDiff ℝ 2 (A z))
    {a b R d D C₀ C₁ M M₁ C κ : ℝ} {α : ℕ → ℝ}
    (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M) (hM₁ : 0 ≤ M₁)
    (hC : 0 ≤ C) (hκ : 0 < κ) (hα : ∀ n, |α n| ≤ C)
    (hfirst : ∀ x ∈ Icc (a-2*R) (b+2*R), |deriv Φ x| ≤ M₁)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ D)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b)
    (hi : ∀ n j, Integrable (fun z => |‖passageCoefficient Φ A κ α n j z‖^2 -
      (n:ℝ)⁻¹*‖passageLeading Φ A a b R κ α n j z‖^2|) μ) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ z,
      |‖passageCoefficient Φ A κ α n j z‖^2 -
        (n:ℝ)⁻¹*‖passageLeading Φ A a b R κ α n j z‖^2| ∂μ) atTop (𝓝 0) := by
  obtain ⟨K₀,hK₀⟩ := exists_nat_ge (2*(C+M₁+1)/κ)
  let K := max K₀ 1
  have hK : 2*(C+M₁+1) ≤ κ*K := by
    have hh : (K₀:ℝ) ≤ K := by exact_mod_cast (le_max_left K₀ 1)
    have hh' := (div_le_iff₀ hκ).mp (hK₀.trans hh)
    nlinarith
  have hK1 : 1 ≤ K := le_max_right _ _
  have hsub : Icc (a-R) (b+R) ⊆ Icc (a-2*R) (b+2*R) := by
    intro x hx; constructor <;> linarith [hx.1,hx.2]
  apply summed_stationary_mass K hK1 (L := C₀ / Real.sqrt (d/(2*Real.pi)))
    (D := 4*(4*C₀+(b-a)*C₁)/κ) (by positivity) hi
    (passage_uniform_error hΦ hA hab hR hd hdD hC₀ hC₁ hM₀ hsecond hupper hM hAb hA'b hsupp κ α)
  · intro n j z
    exact stationaryLeading_bound (hΦ.of_le (by norm_num)) (by linarith) hd hC₀
      (fun x hx => hsecond x (hsub hx)) (fun x hx => hAb z x (hsub hx))
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    intro j hj
    have hb := passage_arrays_tail hΦ hA hab hR hd hC₀ hC₁ hM₁ hC hκ hK hn (hα n)
      hfirst hsecond hAb hA'b hsupp hj
    calc
      _ ≤ ∫ _ : Ω, (4*(4*C₀+(b-a)*C₁)/κ)^2/(j:ℝ)^2 ∂μ :=
        integral_mono (hi n j) (integrable_const _) (by
          intro z
          dsimp only
          rw [(hb z).1, norm_zero, zero_pow (by omega), mul_zero, sub_zero,
            abs_of_nonneg (sq_nonneg _)]
          have hh := sq_le_sq₀ (norm_nonneg (passageCoefficient Φ A κ α n j z)) (by positivity : 0 ≤ (4*(4*C₀+(b-a)*C₁)/κ)/|(j:ℝ)|)
          have hh' := hh.mpr (hb z).2
          simpa only [div_pow, sq_abs] using hh')
      _ = _ := by simp

end ThreeTorus

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Twists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product torus, exact angular packets, all integer twist iterates, and measure-preserving passage charts. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus

lemma continuous_fourier_parseval {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    ∑' j : ℤ, ‖fourierCoeff f j‖^2 =
      ∫ θ : UnitAddCircle, ‖f θ‖^2 ∂AddCircle.haarAddCircle := by
  let F : C(UnitAddCircle,ℂ) := ⟨f,hf⟩
  have hh := tsum_sq_fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ F)
  simp_rw [fourierCoeff_toLp] at hh
  erw [hh]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) AddCircle.haarAddCircle F] with θ hθ
  rw [hθ]
  rfl

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Fourier passage coefficients, branch Jacobians, rounding removal, and integrated stationary mass. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

lemma continuous_fourierCoeff_param {Ω : Type*} [TopologicalSpace Ω]
    [FirstCountableTopology Ω] [LocallyCompactSpace Ω]
    {f : Ω → UnitAddCircle → ℂ} (hf : Continuous f.uncurry) (j : ℤ) :
    Continuous (fun a => fourierCoeff (f a) j) := by
  have hh : Continuous (fun p : Ω × UnitAddCircle => fourier (-j) p.2*f p.1 p.2) :=
    ((fourier (-j)).continuous.comp continuous_snd).mul hf
  simpa only [fourierCoeff,smul_eq_mul,setIntegral_univ] using
    (continuous_parametric_integral_of_continuous (μ := AddCircle.haarAddCircle)
      (f := fun a θ => fourier (-j) θ*f a θ) hh isCompact_univ)

lemma continuous_passageFourierInput {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) :
    Continuous (passageFourierInput m H A).uncurry := by
  exact (hA.comp continuous_swap).mul ((fourier m).continuous.comp (hH.comp continuous_snd))

lemma continuous_exactPassageCoeff {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) (j : ℤ) :
    Continuous (exactPassageCoeff m H A j) :=
  continuous_fourierCoeff_param (continuous_passageFourierInput hH hA) j

end ThreeTorus

namespace ThreeTorus

/-- The exact torus coefficient as a compactly supported real oscillatory integral.
The support hypothesis is the lifted good-arc support, not a Fourier approximation. -/
lemma exactPassageCoeff_real_integral {m j : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {a : UnitAddCircle} {o : ℝ}
    {H₀ : ℝ → ℝ} {A₀ : ℝ → ℂ}
    (hH : ∀ x : ℝ, H (x : UnitAddCircle) = (H₀ x : UnitAddCircle))
    (hA : ∀ x ∈ Ioc o (o+1), A ((x : UnitAddCircle),a) = A₀ x)
    (hAs : Function.support A₀ ⊆ Ioc o (o+1)) :
    exactPassageCoeff m H A j a =
      ∫ x : ℝ, A₀ x*Complex.exp (Complex.I*((2*Real.pi*((m:ℝ)*H₀ x-j*x)):ℝ)) := by
  unfold exactPassageCoeff
  rw [fourierCoeff_eq_intervalIntegral _ _ o]
  simp only [one_div,inv_one,one_smul]
  have he (x : ℝ) (hx : x ∈ Ioc o (o+1)) :
      fourier (-j) (x : UnitAddCircle) • passageFourierInput m H A a (x : UnitAddCircle) =
        A₀ x*Complex.exp (Complex.I*((2*Real.pi*((m:ℝ)*H₀ x-j*x)):ℝ)) := by
    simp only [passageFourierInput,hA x hx,hH x,smul_eq_mul,fourier_coe_apply]
    simp only [Complex.ofReal_one,div_one,Int.cast_neg]
    rw [show Complex.exp (2*Real.pi*Complex.I*(-(j:ℂ))*(x:ℂ))*
        (A₀ x*Complex.exp (2*Real.pi*Complex.I*(m:ℂ)*(H₀ x:ℂ))) =
        A₀ x*(Complex.exp (2*Real.pi*Complex.I*(-(j:ℂ))*(x:ℂ))*
          Complex.exp (2*Real.pi*Complex.I*(m:ℂ)*(H₀ x:ℂ))) by ring,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  calc
    _ = ∫ x in o..o+1, A₀ x*Complex.exp (Complex.I*((2*Real.pi*((m:ℝ)*H₀ x-j*x)):ℝ)) := by
      rw [intervalIntegral.integral_of_le (by linarith : o ≤ o+1),
        intervalIntegral.integral_of_le (by linarith : o ≤ o+1)]
      exact setIntegral_congr_fun measurableSet_Ioc he
    _ = _ := intervalIntegral.integral_eq_integral_of_support_subset (by
      intro x hx
      exact hAs (mul_ne_zero_iff.mp hx).1)

/-- No approximation occurs when the rounded primitive is inserted in the phase.
This is the normalization needed by the compact-support stationary-phase proof. -/
lemma rounded_phase_normalization (m j : ℤ) {n : ℕ} (hn : n ≠ 0)
    (P : ℝ → ℝ) (δ : ℕ → ℝ) (x : ℝ) :
    2*Real.pi*((m:ℝ)*((n:ℝ)*(P x+δ n*x))-(j:ℝ)*x) =
      (n:ℝ)*((2*Real.pi*(m:ℝ)*P x)-
        ((2*Real.pi)*(j:ℝ)/(n:ℝ)-(2*Real.pi*(m:ℝ)*δ n))*x) := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

end ThreeTorus

namespace ThreeTorus

lemma continuous_compact_phase_integral {Ω : Type*} [TopologicalSpace Ω]
    [FirstCountableTopology Ω] [LocallyCompactSpace Ω]
    {A : Ω → ℝ → ℂ} {Φ : ℝ → ℝ} {l u : ℝ}
    (hA : Continuous A.uncurry) (hΦ : Continuous Φ) (hlu : l ≤ u)
    (hs : ∀ a, Function.support (A a) ⊆ Ioc l u) (t : ℝ) :
    Continuous (fun a => ∫ x, A a x*Complex.exp (Complex.I*((t*Φ x):ℝ))) := by
  have hf : Continuous (fun p : Ω × ℝ => A p.1 p.2*Complex.exp (Complex.I*((t*Φ p.2):ℝ))) := by
    fun_prop
  have hh := continuous_parametric_integral_of_continuous
    (μ := (volume : Measure ℝ)) (f := fun a x => A a x*Complex.exp (Complex.I*((t*Φ x):ℝ)))
    hf (isCompact_Icc (a := l) (b := u))
  have he (a : Ω) : (∫ x in Icc l u, A a x*Complex.exp (Complex.I*((t*Φ x):ℝ))) =
      ∫ x, A a x*Complex.exp (Complex.I*((t*Φ x):ℝ)) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hlu]
    exact intervalIntegral_phase_of_support (hs a) Φ t
  simpa only [he] using hh

lemma continuous_passageCoefficient {A : UnitAddCircle → ℝ → ℂ} {Φ : ℝ → ℝ}
    {l u : ℝ} (hA : Continuous A.uncurry) (hΦ : Continuous Φ) (hlu : l ≤ u)
    (hs : ∀ a, Function.support (A a) ⊆ Ioc l u)
    (κ : ℝ) (α : ℕ → ℝ) (n : ℕ) (j : ℤ) :
    Continuous (passageCoefficient Φ A κ α n j) :=
  continuous_compact_phase_integral hA (hΦ.sub (continuous_const.mul continuous_id)) hlu hs n

lemma continuous_passageLeading {A : UnitAddCircle → ℝ → ℂ} {Φ : ℝ → ℝ}
    (hA : Continuous A.uncurry) (l u R κ : ℝ) (α : ℕ → ℝ) (n : ℕ) (j : ℤ) :
    Continuous (passageLeading Φ A l u R κ α n j) := by
  unfold passageLeading stationaryLeading
  split_ifs
  · fun_prop
  · exact continuous_const

/-- Strong summed stationary mass for the actual torus passage coefficients.
All integrability in the slow parameter is derived from compact smooth data. -/
lemma exactPassageCoeff_summed_mass
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R d D C₀ C₁ M M₁ C : ℝ}
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u)
    (hΦ : ContDiff ℝ 3 (fun x => 2*Real.pi*(m:ℝ)*P x))
    (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hC : 0 ≤ C)
    (hδ : ∀ n, |2*Real.pi*(m:ℝ)*δ n| ≤ C)
    (hfirst : ∀ x ∈ Icc (l-2*R) (u+2*R), |deriv (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M₁)
    (hsecond : ∀ x ∈ Icc (l-2*R) (u+2*R), d ≤ iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x)
    (hupper : ∀ x ∈ Icc (l-2*R) (u+2*R), iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x ≤ D)
    (hM : ∀ x ∈ Icc (l-2*R) (u+2*R), |iteratedDeriv 3 (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖A₀ a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖deriv (A₀ a) x‖ ≤ C₁) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*‖passageLeading (fun x => 2*Real.pi*(m:ℝ)*P x) A₀ l u R (2*Real.pi)
          (fun n => 2*Real.pi*(m:ℝ)*δ n) n j a‖^2| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  let Φ : ℝ → ℝ := fun x => 2*Real.pi*(m:ℝ)*P x
  let α : ℕ → ℝ := fun n => 2*Real.pi*(m:ℝ)*δ n
  have hi (n : ℕ) (j : ℤ) : Integrable (fun a =>
      |‖passageCoefficient Φ A₀ (2*Real.pi) α n j a‖^2-
        (n:ℝ)⁻¹*‖passageLeading Φ A₀ l u R (2*Real.pi) α n j a‖^2|)
      AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (((continuous_passageCoefficient hAc hΦ.continuous hlu hsupp _ _ n j).norm.pow 2).sub
      ((continuous_const.mul ((continuous_passageLeading hAc l u R _ α n j).norm.pow 2)))).abs
  have ht := passage_summed_mass (μ := AddCircle.haarAddCircle) hΦ hA₀ hlu hR hd hdD
    hC₀ hC₁ hM₀ hM₁ hC (by positivity : 0 < 2*Real.pi) hδ
    hfirst hsecond hupper hM hAb hA'b hsupp hi
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  congr 1; funext j
  apply integral_congr_ae
  filter_upwards [] with a
  have hs : Function.support (A₀ a) ⊆ Ioc o (o+1) :=
    (hsupp a).trans (Ioc_subset_Ioc hlo huo)
  have he := exactPassageCoeff_real_integral (m := m) (j := j) (H := H n) (A := A)
    (a := a) (hH n) (hA a) hs
  rw [he]
  congr 3
  unfold passageCoefficient passageSlope
  apply congrArg norm
  apply integral_congr_ae
  filter_upwards [] with x
  rw [rounded_phase_normalization m j (by omega : n ≠ 0) P δ x]

open Function

lemma branchDensity_on {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hg : ∀ x ∈ I, g (J x) = x) {x : ℝ} (hx : x ∈ I) :
    branchDensity I J g D q (J x) = q x/|D x| := by
  simp only [branchDensity,indicator_of_mem (mem_image_of_mem J hx),hg x hx]

lemma stationaryLeading_norm_sq_weight {Φ J : ℝ → ℝ} {A : ℝ → ℂ} {l u : ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (hJ : Continuous J) (hlu : l ≤ u)
    (hfirst : ∀ x, deriv Φ x = 2*Real.pi*J x)
    (hsecond : ∀ x, iteratedDeriv 2 Φ x = 2*Real.pi*deriv J x)
    (hpos : ∀ x ∈ Icc l u, 0 < deriv J x) (s t : ℝ) :
    ‖stationaryLeading Φ A l u (2*Real.pi*s) t‖^2 = stationaryWeight (Icc l u) J A s := by
  have hk : 0 < 2*Real.pi := by positivity
  have hmono : StrictMonoOn J (Icc l u) := strictMonoOn_of_deriv_pos (convex_Icc _ _)
    hJ.continuousOn (fun x hx => hpos x (interior_subset hx))
  have himage : J '' Icc l u = Icc (J l) (J u) :=
    hJ.continuousOn.image_Icc_of_monotoneOn hlu hmono.monotoneOn
  have hsiff : 2*Real.pi*s ∈ Icc (deriv Φ l) (deriv Φ u) ↔ s ∈ J '' Icc l u := by
    rw [hfirst l,hfirst u,himage]
    simp only [mem_Icc,mul_le_mul_iff_right₀ hk]
  by_cases hs : s ∈ J '' Icc l u
  · have hsΦ := hsiff.mpr hs
    let v := invFunOn J (Icc l u) s
    have hv : v ∈ Icc l u := (invFunOn_pos hs).1
    have hvJ : J v = s := (invFunOn_pos hs).2
    have hw := stationary_branch_center hΦ hlu hsΦ
    have hinv : invFunOn (deriv Φ) (Icc l u) (2*Real.pi*s) = v := by
      apply hmono.injOn hw.1 hv
      rw [hfirst] at hw
      exact (mul_left_cancel₀ hk.ne' hw.2).trans hvJ.symm
    have hp := hpos v hv
    have hb : iteratedDeriv 2 Φ v/(2*Real.pi) = deriv J v := by
      rw [hsecond]
      field_simp
    rw [norm_stationaryLeading hsΦ,hinv,hb,mul_pow,inv_pow,Real.sq_sqrt hp.le]
    simp only [stationaryWeight,branchDensity,indicator_of_mem hs,abs_of_pos hp,v]
    ring
  · have hsΦ := mt hsiff.mp hs
    simp only [stationaryLeading,ite_eq_right hsΦ,norm_zero,zero_pow (by norm_num : 2 ≠ 0),
      stationaryWeight,branchDensity,indicator_of_notMem hs]

/-- Normalization of the phase derivative agrees exactly with the old speed.
This computes the manuscript's W under the ordinary derivative identity P'=V. -/
lemma phase_speed_derivatives {P V : ℝ → ℝ} {m : ℝ}
    (hP : Differentiable ℝ P) (hV : Differentiable ℝ V) (hPV : deriv P = V) :
    (∀ x, deriv (fun x => 2*Real.pi*m*P x) x = 2*Real.pi*(m*V x)) ∧
    (∀ x, iteratedDeriv 2 (fun x => 2*Real.pi*m*P x) x =
      2*Real.pi*deriv (fun x => m*V x) x) := by
  have hd : deriv (fun x => 2*Real.pi*m*P x) = fun x => 2*Real.pi*m*V x := by
    funext x
    rw [deriv_const_mul (2*Real.pi*m) (hP x),hPV]
  refine ⟨fun x => by rw [hd]; ring,?_⟩
  intro x
  simp only [iteratedDeriv_succ,iteratedDeriv_zero,hd]
  rw [deriv_const_mul (2*Real.pi*m) (hV x),deriv_const_mul m (hV x)]
  ring

/-- Summed stationary mass in the manuscript's actual normalization W, without
an auxiliary complex leading array remaining in the conclusion. -/
lemma exactPassageCoeff_summed_weight
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R d D C₀ C₁ M M₁ C : ℝ}
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u)
    (hΦ : ContDiff ℝ 3 (fun x => 2*Real.pi*(m:ℝ)*P x))
    (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hC : 0 ≤ C)
    (hδ : ∀ n, |2*Real.pi*(m:ℝ)*δ n| ≤ C)
    (hfirst : ∀ x ∈ Icc (l-2*R) (u+2*R), |deriv (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M₁)
    (hsecond : ∀ x ∈ Icc (l-2*R) (u+2*R), d ≤ iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x)
    (hupper : ∀ x ∈ Icc (l-2*R) (u+2*R), iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x ≤ D)
    (hM : ∀ x ∈ Icc (l-2*R) (u+2*R), |iteratedDeriv 3 (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖A₀ a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖deriv (A₀ a) x‖ ≤ C₁) 
    (hP : Differentiable ℝ P) (hV : Differentiable ℝ V) (hPV : deriv P = V) :

    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
          (A₀ a) ((j:ℝ)/n-(m:ℝ)*δ n)| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  have he := phase_speed_derivatives (m := (m:ℝ)) hP hV hPV
  have hi : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    apply Icc_subset_Icc <;> linarith
  have hpos (x : ℝ) (hx : x ∈ Icc (l-R) (u+R)) :
      0 < deriv (fun x => (m:ℝ)*V x) x := by
    have hh := hsecond x (hi hx)
    rw [he.2 x] at hh
    have hk : 0 < 2*Real.pi := by positivity
    nlinarith
  have hweight (n : ℕ) (j : ℤ) (a : UnitAddCircle) :
      ‖passageLeading (fun x => 2*Real.pi*(m:ℝ)*P x) A₀ l u R (2*Real.pi)
        (fun n => 2*Real.pi*(m:ℝ)*δ n) n j a‖^2 =
      stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a)
        ((j:ℝ)/n-(m:ℝ)*δ n) := by
    unfold passageLeading passageSlope
    have hs : 2*Real.pi*(j:ℝ)/(n:ℝ)-2*Real.pi*(m:ℝ)*δ n =
        2*Real.pi*((j:ℝ)/n-(m:ℝ)*δ n) := by ring
    rw [hs]
    exact stationaryLeading_norm_sq_weight (hΦ.of_le (by norm_num))
      (continuous_const.mul hV.continuous) (by linarith) he.1 he.2 hpos _ _
  have hh := exactPassageCoeff_summed_mass hH hA hA₀ hAc hsupp hlo huo hlu
    hΦ hR hd hdD hC₀ hC₁ hM₀ hM₁ hC hδ hfirst hsecond hupper hM hAb hA'b
  simp_rw [hweight] at hh
  exact hh

lemma continuous_fourier_summable {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    Summable (fun j : ℤ => ‖fourierCoeff f j‖^2) := by
  let F : C(UnitAddCircle,ℂ) := ⟨f,hf⟩
  have hh := (hasSum_sq_fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ F)).summable
  simpa only [fourierCoeff_toLp, F, ContinuousMap.coe_mk] using hh

/-- The integrated Fourier masses really are summable, so no use of a default
zero value of a divergent tsum is possible in the passage estimates. -/
lemma continuous_family_fourier_summable {f : UnitAddCircle → UnitAddCircle → ℂ}
    (hf : Continuous f.uncurry) :
    Summable (fun j : ℤ => ∫ a : UnitAddCircle, ‖fourierCoeff (f a) j‖^2
      ∂AddCircle.haarAddCircle) := by
  have hfi (a : UnitAddCircle) : Continuous (f a) := hf.comp (continuous_const.prodMk continuous_id)
  have hj (j : ℤ) : Integrable (fun a => ‖fourierCoeff (f a) j‖^2) AddCircle.haarAddCircle :=
    ((continuous_fourierCoeff_param hf j).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hec : Continuous (fun a : UnitAddCircle => ∫ θ : UnitAddCircle, ‖f a θ‖^2
      ∂AddCircle.haarAddCircle) := by
    simpa only [setIntegral_univ] using
      (continuous_parametric_integral_of_continuous (μ := AddCircle.haarAddCircle)
        (f := fun a θ => ‖f a θ‖^2) (by exact hf.norm.pow 2) isCompact_univ)
  have hei := hec.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  apply summable_of_sum_le (c := ∫ a : UnitAddCircle,
    (∫ θ : UnitAddCircle, ‖f a θ‖^2 ∂AddCircle.haarAddCircle) ∂AddCircle.haarAddCircle)
  · intro j
    exact integral_nonneg (fun _ => sq_nonneg _)
  · intro S
    rw [← integral_finsetSum _ (fun j _ => hj j)]
    apply integral_mono (integrable_finsetSum S (fun j _ => hj j)) hei
    intro a
    dsimp only
    rw [← continuous_fourier_parseval (hfi a)]
    exact (continuous_fourier_summable (hfi a)).sum_le_tsum S (fun _ _ => sq_nonneg _)

lemma exactPassageCoeff_summable {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) :
    Summable (fun j : ℤ => ∫ a : UnitAddCircle, ‖exactPassageCoeff m H A j a‖^2
      ∂AddCircle.haarAddCircle) := by
  exact continuous_family_fourier_summable (continuous_passageFourierInput hH hA)

lemma contDiffAt_invFunOn_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hinj : InjOn J I) {x d : ℝ} (hx : x ∈ I)
    (hd : HasDerivAt J d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFunOn J I) (J x) := by
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (J x) := by
    apply e.contDiffAt_symm_deriv hd0 hyt
    · simpa only [he,hix] using hd
    · simpa only [he,hix] using hJ.contDiffAt (x := x)
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply hi.continuousAt.eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  have hr : J (e.symm y) = y := by simpa only [he] using e.right_inv hy
  have hp := invFunOn_pos (show y ∈ J '' I from ⟨e.symm y,hyI,hr⟩)
  exact hinj hp.1 hyI (hp.2.trans hr.symm)

lemma isOpen_image_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hd : ∀ x ∈ I, deriv J x ≠ 0) : IsOpen (J '' I) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x,hx,rfl⟩
  have hdx := (hJ.differentiable (by simp) x).hasDerivAt
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply (e.continuousAt_symm hyt).eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  exact ⟨e.symm y,hyI,by simpa only [he] using e.right_inv hy⟩

lemma support_branchFamily_subset {Ω : Type*} [TopologicalSpace Ω]
    {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ} :
    support (branchFamily I J F) ⊆ (fun p : ℝ × Ω => (J p.1,p.2)) '' tsupport F := by
  rintro ⟨s,a⟩ hh
  have hs : s ∈ J '' I := by
    by_contra hn
    exact hh (by simp [branchFamily,hn])
  have hp := invFunOn_pos hs
  refine ⟨(invFunOn J I s,a),subset_tsupport F ?_,?_⟩
  · intro hz
    exact hh (by simp [branchFamily,hs,hz])
  · simp only [hp.2]

lemma branchFamily_compact {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) : HasCompactSupport (branchFamily I J F) := by
  apply HasCompactSupport.intro (hc.image (by fun_prop : Continuous (fun p : ℝ × Ω => (J p.1,p.2))))
  intro p hp
  by_contra hn
  exact hp (support_branchFamily_subset hn)

lemma branchFamily_continuous {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × Ω → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : Continuous F) (hc : HasCompactSupport F) (hs : tsupport F ⊆ I ×ˢ univ) :
    Continuous (branchFamily I J F) := by
  classical
  let g := invFunOn J I
  let M := (fun p : ℝ × Ω => (J p.1,p.2)) '' tsupport F
  have hM : IsCompact M := hc.image (by fun_prop)
  have hzero {p : ℝ × Ω} (hp : p ∉ M) : branchFamily I J F p = 0 :=
    notMem_support.mp (fun hn => hp (support_branchFamily_subset hn))
  have hD : Continuous (deriv J) := hJ.continuous_deriv (by simp)
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ M
  · rcases hp with ⟨⟨x,a⟩,hx,rfl⟩
    have hxI : x ∈ I := (hs hx).1
    have hy : J x ∈ J '' I := mem_image_of_mem J hxI
    have hgi := (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)).continuousAt
    have hge : g (J x) = x := by
      exact hinj (invFunOn_pos hy).1 hxI (invFunOn_pos hy).2
    have hgi' : ContinuousAt (fun p : ℝ × Ω => g p.1) (J x,a) :=
      hgi.comp_of_eq continuousAt_fst rfl
    have hin : ContinuousAt (fun p : ℝ × Ω => (g p.1,p.2)) (J x,a) :=
      hgi'.prodMk continuousAt_snd
    have hDen : ContinuousAt (fun p : ℝ × Ω => |deriv J (g p.1)|) (J x,a) :=
      (hD.continuousAt.comp hgi').abs
    have hquot : ContinuousAt (fun p : ℝ × Ω => F (g p.1,p.2) / |deriv J (g p.1)|) (J x,a) := by
      apply (hF.continuousAt.comp hin).div hDen
      simpa only [hge] using abs_ne_zero.mpr (hd x hxI)
    apply hquot.congr_of_eventuallyEq
    have hnear : ∀ᶠ p : ℝ × Ω in 𝓝 (J x,a), p.1 ∈ J '' I :=
      continuous_fst.continuousAt.eventually ((isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hy)
    filter_upwards [hnear] with p hp
    simp only [branchFamily,ite_eq_left hp,g]
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hzero hq

lemma branchFamily_congr_branch {Ω : Type*} {C I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hIC : I ⊆ C) (hinj : InjOn J C) (hs : support F ⊆ I ×ˢ univ) :
    branchFamily C J F = branchFamily I J F := by
  classical
  funext p
  have him : J '' I ⊆ J '' C := image_mono hIC
  by_cases hp : p.1 ∈ J '' C
  · have hc := invFunOn_pos hp
    by_cases hpi : p.1 ∈ J '' I
    · have hi := invFunOn_pos hpi
      have hinv : invFunOn J C p.1 = invFunOn J I p.1 :=
        hinj hc.1 (hIC hi.1) (hc.2.trans hi.2.symm)
      simp [branchFamily,hp,hpi,hinv]
    · have hz : F (invFunOn J C p.1,p.2) = 0 := by
        by_contra hn
        exact hpi ⟨_, (hs hn).1, hc.2⟩
      simp [branchFamily,hp,hpi,hz]
  · have hpi : p.1 ∉ J '' I := fun h => hp (him h)
    simp [branchFamily,hp,hpi]

lemma stationaryWeight_family_eq (C : Set ℝ) (J : ℝ → ℝ)
    (A : UnitAddCircle → ℝ → ℂ) :
    (fun p : ℝ × UnitAddCircle => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × UnitAddCircle => ‖A p.2 p.1‖^2) := by
  classical
  funext p
  by_cases hp : p.1 ∈ J '' C <;> simp [stationaryWeight,branchDensity,branchFamily,hp]

/-- Joint compact continuity of the exact density used in stationary phase.
The enlarged stationary branch creates no boundary discontinuity because the
original packet is supported in the strictly smaller closed interval. -/
lemma stationaryWeight_compact_continuous {J : ℝ → ℝ}
    {A : UnitAddCircle → ℝ → ℂ} {l u R : ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hA : Continuous A.uncurry) (hs : ∀ a, support (A a) ⊆ Icc l u)
    (hR : 0 < R) (hd : ∀ x ∈ Icc (l-R) (u+R), 0 < deriv J x) :
    Continuous (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) ∧
    HasCompactSupport (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) := by
  let F : ℝ × UnitAddCircle → ℝ := fun p => ‖A p.2 p.1‖^2
  have hF : Continuous F := (hA.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2
  have hFs : support F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) := by
    intro p hp
    refine ⟨hs p.2 ?_,mem_univ _⟩
    by_contra hn
    have hz : A p.2 p.1 = 0 := notMem_support.mp hn
    exact hp (by simp [F,hz])
  have hFt : tsupport F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) :=
    closure_minimal hFs (isClosed_Icc.prod isClosed_univ)
  have hc : HasCompactSupport F :=
    (isCompact_Icc.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport F) hFt
  let C := Icc (l-R) (u+R)
  let I := Ioo (l-R) (u+R)
  have hIC : I ⊆ C := Ioo_subset_Icc_self
  have hinj : InjOn J C := (strictMonoOn_of_deriv_pos (convex_Icc _ _)
    hJ.continuous.continuousOn (fun x hx => hd x (interior_subset hx))).injOn
  have hsub : Icc l u ⊆ I := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hFtI : tsupport F ⊆ I ×ˢ (univ : Set UnitAddCircle) :=
    fun p hp => ⟨hsub (hFt hp).1,mem_univ _⟩
  have he := branchFamily_congr_branch hIC hinj (subset_trans subset_closure hFtI)
  rw [stationaryWeight_family_eq]
  change Continuous (branchFamily C J F) ∧ HasCompactSupport (branchFamily C J F)
  refine ⟨?_,branchFamily_compact hJ.continuous hc⟩
  rw [he]
  exact branchFamily_continuous hJ isOpen_Ioo (hinj.mono hIC)
    (fun x hx => (hd x (hIC hx)).ne') hF hc hFtI

open scoped NNReal

lemma roundingMass_uniform_bound {W : ℝ → UnitAddCircle → ℝ} {A C e η : ℝ} {K n : ℕ}
    (hW : Continuous W.uncurry) (hη : 0 ≤ η)
    (hclose : ∀ s a, |W (s-e) a-W s a| ≤ η)
    (hs : ∀ s a, A < |s| → W s a = 0)
    (he : |e| ≤ C) (hK : A+C ≤ K) (hn : 0 < n) :
    roundingMass W n e ≤ (2*(K:ℝ)+1)*η := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hC : 0 ≤ C := (abs_nonneg e).trans he
  let S : Finset ℤ := Finset.Icc (-(K*n:ℤ)) (K*n)
  have hz (j : ℤ) (hj : j ∉ S) (a : UnitAddCircle) :
      |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a| = 0 := by
    have hj' : (K:ℝ)*n < |(j:ℝ)| := by
      have hh : (K*n:ℤ) < |j| := by
        simpa only [S,Finset.mem_Icc,← abs_le,not_le] using hj
      exact_mod_cast hh
    have hjn : (K:ℝ) < |(j:ℝ)/n| := by
      rw [abs_div,abs_of_pos hn']
      exact (lt_div_iff₀ hn').mpr hj'
    have hje : A < |(j:ℝ)/n-e| := by
      have hb := abs_add_le ((j:ℝ)/n-e) e
      rw [sub_add_cancel] at hb
      linarith
    have hja : A < |(j:ℝ)/n| := by linarith
    rw [hs _ _ hje,hs _ _ hja,sub_self,abs_zero]
  have heq : (∑' j : ℤ, ∫ a : UnitAddCircle,
      |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) =
      ∑ j ∈ S, ∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a|
        ∂AddCircle.haarAddCircle := by
    apply tsum_eq_sum
    intro j hj
    simp only [hz j hj,integral_zero]
  have hb (j : ℤ) : (∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a|
      ∂AddCircle.haarAddCircle) ≤ η := by
    have hc : Continuous (fun a : UnitAddCircle => |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a|) := by
      fun_prop
    calc
      _ ≤ ∫ _ : UnitAddCircle, η ∂AddCircle.haarAddCircle :=
        integral_mono (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (integrable_const _) (fun a => hclose _ a)
      _ = _ := by simp
  have hcard : (S.card:ℝ) = 2*(K:ℝ)*n+1 := by
    have hc : S.card = 2*(K*n)+1 := by
      dsimp only [S]
      rw [Int.card_Icc]
      have hz : (K:ℤ)*n + 1 - -((K:ℤ)*n) = ((2*(K*n)+1:ℕ):ℤ) := by
        push_cast
        ring
      rw [hz, Int.toNat_natCast]
    rw [hc]
    push_cast
    ring
  unfold roundingMass
  rw [heq]
  calc
    _ ≤ (n:ℝ)⁻¹ * (S.card*(η)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn'.le)
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (fun j _ => hb j)
    _ = (2*(K:ℝ)+(n:ℝ)⁻¹)*η := by rw [hcard]; field_simp
    _ ≤ _ := by
      have hi : (n:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      exact mul_le_mul_of_nonneg_right (by linarith) hη

/-- Compact continuity is sufficient for removal of rounding; no quantitative
Lipschitz hypothesis has to be added to the old spectral density. -/
lemma tendsto_roundingMass_of_compact {W : ℝ → UnitAddCircle → ℝ} {e : ℕ → ℝ}
    (hW : Continuous W.uncurry) (hc : HasCompactSupport W.uncurry)
    (ht : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => roundingMass W n (e n)) atTop (𝓝 0) := by
  have hUC := hc.uniformContinuous_of_continuous hW
  obtain ⟨R,hR⟩ := (hc.image continuous_fst).isBounded.subset_closedBall (0 : ℝ)
  let A := max R 0
  have hs (s a) (hs : A < |s|) : W s a = 0 := by
    by_contra hn
    have hh := hR ⟨(s,a),subset_tsupport _ hn,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] at hh
    exact (not_lt_of_ge (hh.trans (le_max_left _ _))) hs
  obtain ⟨K,hK⟩ := exists_nat_ge (A+1)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C : ℝ := 2*(K:ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  let η : ℝ := ε/(2*C)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp hUC η hη
  have he : ∀ᶠ n in atTop, |e n| < min δ 1 := by
    simpa only [Real.dist_eq,sub_zero] using Metric.tendsto_nhds.mp ht (min δ 1) (lt_min hδ zero_lt_one)
  filter_upwards [he,eventually_gt_atTop (0:ℕ)] with n hn hn0
  have hb := roundingMass_uniform_bound (K := K) hW hη.le
    (fun s a => le_of_lt (hclose (a := (s-e n,a)) (b := (s,a)) (by
      simpa only [Prod.dist_eq,dist_self,Real.dist_eq,sub_sub_cancel_left,abs_neg,max_eq_left (abs_nonneg (e n))] using
        (lt_of_lt_of_le hn (min_le_left _ _))))) hs
    (show |e n| ≤ 1 from le_of_lt (lt_of_lt_of_le hn (min_le_right _ _))) hK hn0
  have hnonneg : 0 ≤ roundingMass W n (e n) := by
    unfold roundingMass
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (tsum_nonneg (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hnonneg]
  have heq : (2*(K:ℝ)+1)*η = ε/2 := by dsimp [η,C]; field_simp
  exact (hb.trans_eq heq).trans_lt (by linarith)

lemma compact_lattice_support {W : ℝ → UnitAddCircle → ℝ} (hc : HasCompactSupport W.uncurry)
    {n : ℕ} (hn : 0 < n) (e : ℝ) :
    ∃ S : Finset ℤ, ∀ j ∉ S, ∀ a, W ((j:ℝ)/n-e) a = 0 := by
  obtain ⟨R,hR⟩ := (hc.image continuous_fst).isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨K,hK⟩ := exists_nat_ge (R+|e|)
  refine ⟨Finset.Icc (-(K*n:ℤ)) (K*n),?_⟩
  intro j hj a
  by_contra hz
  have hh := hR ⟨((j:ℝ)/n-e,a),subset_tsupport _ hz,rfl⟩
  rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] at hh
  have hjn : (K:ℝ) < |(j:ℝ)/n| := by
    have hk : (K*n:ℤ) < |j| := by
      simpa only [Finset.mem_Icc,← abs_le,not_le] using hj
    have hk' : (K:ℝ)*n < |(j:ℝ)| := by exact_mod_cast hk
    rw [abs_div,abs_of_pos (show (0:ℝ) < n by exact_mod_cast hn)]
    exact (lt_div_iff₀ (by exact_mod_cast hn)).mpr hk'
  have ht := abs_add_le ((j:ℝ)/n-e) e
  rw [sub_add_cancel] at ht
  linarith

lemma compact_lattice_summable_integral {W : ℝ → UnitAddCircle → ℝ}
    (hc : HasCompactSupport W.uncurry) {n : ℕ} (hn : 0 < n) (e : ℝ) :
    Summable (fun j : ℤ => ∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a|
      ∂AddCircle.haarAddCircle) := by
  obtain ⟨S,hS⟩ := compact_lattice_support hc hn e
  apply summable_of_ne_finset_zero (s := S)
  intro j hj
  simp only [hS j hj,abs_zero,integral_zero]

lemma integrated_array_mass_error_summable {c : ℤ → UnitAddCircle → ℂ}
    {W : ℝ → UnitAddCircle → ℝ} (hW : Continuous W.uncurry)
    (hc : HasCompactSupport W.uncurry) (hcc : ∀ j, Continuous (c j))
    (hcs : Summable (fun j : ℤ => ∫ a : UnitAddCircle, ‖c j a‖^2 ∂AddCircle.haarAddCircle))
    {n : ℕ} (hn : 0 < n) (e : ℝ) :
    Summable (fun j : ℤ => ∫ a : UnitAddCircle,
      |‖c j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e) a| ∂AddCircle.haarAddCircle) := by
  have hp (j : ℤ) : Continuous (fun a => W ((j:ℝ)/n-e) a) :=
    hW.comp (continuous_const.prodMk continuous_id)
  have he (j : ℤ) : Integrable (fun a => |‖c j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e) a|)
      AddCircle.haarAddCircle :=
    (((hcc j).norm.pow 2).sub (continuous_const.mul (hp j))).abs.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi (j : ℤ) : Integrable (fun a => ‖c j a‖^2+(n:ℝ)⁻¹*|W ((j:ℝ)/n-e) a|)
      AddCircle.haarAddCircle :=
    (((hcc j).norm.pow 2).add (continuous_const.mul (hp j).abs)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply Summable.of_nonneg_of_le (fun j => integral_nonneg (fun a => abs_nonneg _))
    (f := fun j => (∫ a : UnitAddCircle, ‖c j a‖^2 ∂AddCircle.haarAddCircle)+
      (n:ℝ)⁻¹*(∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a| ∂AddCircle.haarAddCircle))
  · intro j
    rw [← integral_const_mul,← integral_add]
    · exact integral_mono (he j) (hi j) (fun a => by
        calc
          _ ≤ |‖c j a‖^2|+|(n:ℝ)⁻¹*W ((j:ℝ)/n-e) a| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))])
    · exact ((hcc j).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact (continuous_const.mul (hp j).abs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hcs.add ((compact_lattice_summable_integral hc hn e).mul_left _)

/-- Removal of rounding for actual coefficient masses, with all summability
proved from compact support and true squared Fourier mass. -/
lemma remove_array_rounding {c : ℕ → ℤ → UnitAddCircle → ℂ}
    {W : ℝ → UnitAddCircle → ℝ} {e : ℕ → ℝ}
    (hW : Continuous W.uncurry) (hc : HasCompactSupport W.uncurry)
    (hcc : ∀ n j, Continuous (c n j))
    (hcs : ∀ n, Summable (fun j : ℤ => ∫ a : UnitAddCircle, ‖c n j a‖^2 ∂AddCircle.haarAddCircle))
    (he : Tendsto e atTop (𝓝 0))
    (ht : Tendsto (fun n => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a| ∂AddCircle.haarAddCircle) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) atTop (𝓝 0) := by
  have hr := tendsto_roundingMass_of_compact hW hc he
  have hbound : ∀ᶠ n in atTop,
      (∑' j : ℤ, ∫ a : UnitAddCircle, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) ≤
      (∑' j : ℤ, ∫ a : UnitAddCircle, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a| ∂AddCircle.haarAddCircle)+
        roundingMass W n (e n) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hinv : 0 ≤ (n:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
    have hs₀ := integrated_array_mass_error_summable hW hc (hcc n) (hcs n) hn 0
    simp only [sub_zero] at hs₀
    have hs₁ := integrated_array_mass_error_summable hW hc (hcc n) (hcs n) hn (e n)
    have hs₂ : Summable (fun j : ℤ => ∫ a : UnitAddCircle,
        |W ((j:ℝ)/n-e n) a-W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) := by
      obtain ⟨S,hS⟩ := compact_lattice_support hc hn (e n)
      obtain ⟨T,hT⟩ := compact_lattice_support hc hn 0
      apply summable_of_ne_finset_zero (s := S ∪ T)
      intro j hj
      have hjS : j ∉ S := fun h => hj (Finset.mem_union_left T h)
      have hjT : j ∉ T := fun h => hj (Finset.mem_union_right S h)
      have hz (a) : W ((j:ℝ)/n) a = 0 := by simpa only [sub_zero] using hT j hjT a
      simp only [hS j hjS,hz,sub_self,abs_zero,integral_zero]
    have hi (j : ℤ) :
        (∫ a : UnitAddCircle, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) ≤
        (∫ a : UnitAddCircle, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a| ∂AddCircle.haarAddCircle)+
          (n:ℝ)⁻¹*(∫ a : UnitAddCircle, |W ((j:ℝ)/n-e n) a-W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) := by
      have h₀ : Continuous (fun a => W ((j:ℝ)/n) a) := hW.comp (continuous_const.prodMk continuous_id)
      have h₁ : Continuous (fun a => W ((j:ℝ)/n-e n) a) := hW.comp (continuous_const.prodMk continuous_id)
      have hcj := ((hcc n j).norm.pow 2)
      rw [← integral_const_mul,← integral_add]
      · apply integral_mono
        · exact (hcj.sub (continuous_const.mul h₀)).abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        · exact ((hcj.sub (continuous_const.mul h₁)).abs.add
            (continuous_const.mul (h₁.sub h₀).abs)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        · intro a
          calc
            _ ≤ |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a|+
                |(n:ℝ)⁻¹*(W ((j:ℝ)/n-e n) a-W ((j:ℝ)/n) a)| := by
              convert abs_add_le (‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a)
                ((n:ℝ)⁻¹*(W ((j:ℝ)/n-e n) a-W ((j:ℝ)/n) a)) using 1
              all_goals try with_reducible_and_instances rfl
              ring_nf
            _ = _ := by rw [abs_mul,abs_of_nonneg hinv]
      · exact (hcj.sub (continuous_const.mul h₁)).abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact (continuous_const.mul (h₁.sub h₀).abs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hh := Summable.tsum_le_tsum hi hs₀ (hs₁.add (hs₂.mul_left _))
    rw [hs₁.tsum_add (hs₂.mul_left _),tsum_mul_left] at hh
    exact hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => tsum_nonneg (fun j => integral_nonneg (fun a => abs_nonneg _)))) hbound
  simpa only [add_zero] using ht.add hr

lemma exactPassageCoeff_summed_unrounded
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R d D C₀ C₁ M M₁ C : ℝ}
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u)
    (hΦ : ContDiff ℝ 3 (fun x => 2*Real.pi*(m:ℝ)*P x))
    (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hC : 0 ≤ C)
    (hδ : ∀ n, |2*Real.pi*(m:ℝ)*δ n| ≤ C)
    (hfirst : ∀ x ∈ Icc (l-2*R) (u+2*R), |deriv (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M₁)
    (hsecond : ∀ x ∈ Icc (l-2*R) (u+2*R), d ≤ iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x)
    (hupper : ∀ x ∈ Icc (l-2*R) (u+2*R), iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x ≤ D)
    (hM : ∀ x ∈ Icc (l-2*R) (u+2*R), |iteratedDeriv 3 (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖A₀ a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖deriv (A₀ a) x‖ ≤ C₁) 
    (hP : Differentiable ℝ P) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv P = V)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0)) :

    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
          (A₀ a) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  have hVr := hV.differentiable (by simp)
  have ht := exactPassageCoeff_summed_weight hH hA hA₀ hAc hsupp hlo huo hlu
    hΦ hR hd hdD hC₀ hC₁ hM₀ hM₁ hC hδ hfirst hsecond hupper hM hAb hA'b hP hVr hPV
  let W : ℝ → UnitAddCircle → ℝ := fun s a =>
    stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s
  have he := phase_speed_derivatives (m := (m:ℝ)) hP hVr hPV
  have hi : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    apply Icc_subset_Icc <;> linarith
  have hp (x : ℝ) (hx : x ∈ Icc (l-R) (u+R)) :
      0 < deriv (fun x => (m:ℝ)*V x) x := by
    have hh := hsecond x (hi hx)
    rw [he.2 x] at hh
    have hk : 0 < 2*Real.pi := by positivity
    nlinarith
  have hW := stationaryWeight_compact_continuous (contDiff_const.mul hV) hAc
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hR hp
  simpa only [W] using remove_array_rounding (c := fun n j => exactPassageCoeff m (H n) A j)
    (W := W) hW.1 hW.2 (fun n j => continuous_exactPassageCoeff (hHc n) hAcont j)
    (fun n => exactPassageCoeff_summable (hHc n) hAcont)
    (show Tendsto (fun n => (m:ℝ)*δ n) atTop (𝓝 0) from by simpa using hδt.const_mul (m:ℝ)) ht

end ThreeTorus

namespace ThreeTorus

/-- A compact positive second derivative supplies every numerical constant used
by the uniform stationary-phase estimate.  None of those constants are extra
hypotheses of the passage. -/
lemma exactPassageCoeff_summed_positive
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : 0 < m)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv P = V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
          (A₀ a) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  let Φ : ℝ → ℝ := fun x => 2*Real.pi*(m:ℝ)*P x
  let K : Set ℝ := Icc (l-2*R) (u+2*R)
  have hK : IsCompact K := isCompact_Icc
  have hKne : K.Nonempty := nonempty_Icc.mpr (by linarith)
  have hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := contDiff_const.mul hP
  have he := phase_speed_derivatives (m := (m:ℝ)) (hP.differentiable (by simp))
    (hV.differentiable (by simp)) hPV
  have hpos (x : ℝ) (hx : x ∈ K) : 0 < iteratedDeriv 2 Φ x := by
    rw [he.2 x,deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_pos (by positivity) (mul_pos (by exact_mod_cast hm) (hd x hx))
  obtain ⟨x₀,hx₀,hmin⟩ := hK.exists_isMinOn hKne
    (hΦ.continuous_iteratedDeriv 2 (by exact WithTop.coe_le_coe.mpr le_top)).continuousOn
  let d := iteratedDeriv 2 Φ x₀
  have hd0 : 0 < d := hpos x₀ hx₀
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (hΦ.continuous_iteratedDeriv 2 (by exact WithTop.coe_le_coe.mpr le_top)).continuousOn
  obtain ⟨M₁,hM₁⟩ := hK.exists_bound_of_continuousOn
    (hΦ.continuous_deriv (by simp)).continuousOn
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn
    (hΦ.continuous_iteratedDeriv 3 (by exact WithTop.coe_le_coe.mpr le_top)).continuousOn
  obtain ⟨C₀,hC₀⟩ := (isCompact_univ.prod hK).exists_bound_of_continuousOn hAc.continuousOn
  obtain ⟨C₁,hC₁⟩ := (isCompact_univ.prod hK).exists_bound_of_continuousOn hAd.continuousOn
  have hδb : BddAbove (range (fun n => |2*Real.pi*(m:ℝ)*δ n|)) :=
    ((hδt.const_mul (2*Real.pi*(m:ℝ))).abs).bddAbove_range
  obtain ⟨C,hC⟩ := hδb
  apply exactPassageCoeff_summed_unrounded hH hA hA₀ hAc hsupp hlo huo hlu
    (hΦ.of_le (by exact WithTop.coe_le_coe.mpr le_top)) hR hd0
    (d := d) (D := max 0 D) (C₀ := max 0 C₀) (C₁ := max 0 C₁)
    (M := max 0 M) (M₁ := max 0 M₁) (C := max 0 C)
  · exact (le_abs_self _).trans ((hD x₀ hx₀).trans (le_max_right _ _))
  · exact le_max_left _ _
  · exact le_max_left _ _
  · exact le_max_left _ _
  · exact le_max_left _ _
  · exact le_max_left _ _
  · intro n
    exact (hC (mem_range_self n)).trans (le_max_right _ _)
  · intro x hx
    exact (hM₁ x hx).trans (le_max_right _ _)
  · intro x hx
    exact hmin hx
  · intro x hx
    exact (le_abs_self _).trans ((hD x hx).trans (le_max_right _ _))
  · intro x hx
    exact (hM x hx).trans (le_max_right _ _)
  · intro a x hx
    exact (hC₀ (a,x) ⟨mem_univ _,hx⟩).trans (le_max_right _ _)
  · intro a x hx
    exact (hC₁ (a,x) ⟨mem_univ _,hx⟩).trans (le_max_right _ _)
  · exact hP.differentiable (by simp)
  · exact hV
  · exact hPV
  · exact hHc
  · exact hAcont
  · exact hδt

end ThreeTorus

namespace ThreeTorus
open Function
open scoped ComplexConjugate

lemma exactPassageCoeff_neg (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (a : UnitAddCircle) :
    exactPassageCoeff (-m) H (fun x => conj (A x)) j a =
      conj (exactPassageCoeff m H A (-j) a) := by
  unfold exactPassageCoeff fourierCoeff passageFourierInput
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with θ
  simp only [smul_eq_mul, neg_neg, map_mul, fourier_neg]

lemma exactPassageCoeff_neg_norm (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (a : UnitAddCircle) :
    ‖exactPassageCoeff (-m) H (fun x => conj (A x)) j a‖ =
      ‖exactPassageCoeff m H A (-j) a‖ := by
  rw [exactPassageCoeff_neg,Complex.norm_conj]

lemma summed_mass_reflect (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (W : ℝ → UnitAddCircle → ℝ) (n : ℕ) :
    (∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff (-m) H (fun x => conj (A x)) j a‖^2-
        (n:ℝ)⁻¹*W (-(j:ℝ)/n) a| ∂AddCircle.haarAddCircle) =
    (∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m H A j a‖^2-
        (n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) := by
  simp_rw [exactPassageCoeff_neg_norm]
  simpa only [Int.cast_neg] using
    tsum_comp_neg (fun j : ℤ => ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m H A j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a|
        ∂AddCircle.haarAddCircle)

lemma stationaryWeight_reflect {I : Set ℝ} {J : ℝ → ℝ}
    (hinj : InjOn J I) (A : ℝ → ℂ) (s : ℝ) :
    stationaryWeight I (fun x => -J x) (fun x => conj (A x)) s =
      stationaryWeight I J A (-s) := by
  classical
  have hi : InjOn (fun x => -J x) I := fun x hx y hy he => hinj hx hy (neg_injective he)
  by_cases hs : -s ∈ J '' I
  · obtain ⟨x,hx,hxs⟩ := hs
    have hneg : -J x = s := by linarith
    have hm : s ∈ (fun x => -J x) '' I := ⟨x,hx,hneg⟩
    have h₁ : invFunOn (fun x => -J x) I s = x := by
      rw [← hneg]; exact hi.leftInvOn_invFunOn hx
    have h₂ : invFunOn J I (-s) = x := by
      rw [← hxs]; exact hinj.leftInvOn_invFunOn hx
    simp only [stationaryWeight,branchDensity,indicator_of_mem hm,
      indicator_of_mem (show -s ∈ J '' I from ⟨x,hx,hxs⟩),h₁,h₂,
      Complex.norm_conj]
    change ‖A x‖^2/|deriv (-J) x| = ‖A x‖^2/|deriv J x|
    rw [deriv.neg,abs_neg]
  · have hm : s ∉ (fun x => -J x) '' I := by
      rintro ⟨x,hx,he⟩
      exact hs ⟨x,hx,by linarith⟩
    simp only [stationaryWeight,branchDensity,indicator_of_notMem hm,indicator_of_notMem hs]

/-- The source passage mass theorem at every nonzero angular index. -/
lemma exactPassageCoeff_summed
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv P = V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
          (A₀ a) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  rcases lt_or_gt_of_ne hm with hm | hm
  · have hm' : 0 < -m := neg_pos.mpr hm
    have hconjA₀ (a : UnitAddCircle) : ContDiff ℝ 2 (fun x => conj (A₀ a x)) :=
      Complex.conjCLE.contDiff.comp (hA₀ a)
    have hconjAc : Continuous (fun p : UnitAddCircle × ℝ => conj (A₀ p.1 p.2)) :=
      Complex.continuous_conj.comp hAc
    have hconjAd : Continuous (fun p : UnitAddCircle × ℝ =>
        deriv (fun x => conj (A₀ p.1 x)) p.2) := by
      simpa only [show ∀ z : ℂ, conj z = star z from fun _ => rfl, deriv.star]
        using hAd.star
    have hs := exactPassageCoeff_summed_positive (A := fun x => conj (A x))
      (A₀ := fun a x => conj (A₀ a x)) hm' hH
      (fun a x hx => congrArg (conj : ℂ → ℂ) (hA a x hx))
      hconjA₀ hconjAc hconjAd
      (fun a x hx => hsupp a (by simpa using hx))
      hlo huo hlu hR hP hV hPV hd hHc (Complex.continuous_conj.comp hAcont) hδt
    have hJ : InjOn (fun x => (-m:ℝ)*V x) (Icc (l-R) (u+R)) := by
      apply StrictMonoOn.injOn
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        ((contDiff_const.mul hV).continuous.continuousOn)
      intro x hx
      rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
      exact mul_pos (by exact_mod_cast hm') (hd x (by
        have hx' := interior_subset hx
        constructor <;> linarith [hx'.1,hx'.2]))
    have href (a : UnitAddCircle) (s : ℝ) :
        stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s =
        stationaryWeight (Icc (l-R) (u+R)) (fun x => (-m:ℝ)*V x)
          (fun x => conj (A₀ a x)) (-s) := by
      simpa only [neg_mul, neg_neg, starRingEnd_self_apply] using
        stationaryWeight_reflect hJ (fun x => conj (A₀ a x)) s
    have he (n : ℕ) :
        (∑' j : ℤ, ∫ a : UnitAddCircle,
          |‖exactPassageCoeff m (H n) A j a‖^2-
            (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
              (A₀ a) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle) =
        (∑' j : ℤ, ∫ a : UnitAddCircle,
          |‖exactPassageCoeff (-m) (H n) (fun x => conj (A x)) j a‖^2-
            (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (-m:ℝ)*V x)
              (fun x => conj (A₀ a x)) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle) := by
      simp_rw [href]
      simpa only [neg_neg,starRingEnd_self_apply, Int.cast_neg, neg_div] using
        summed_mass_reflect (-m) (H n) (fun x => conj (A x))
          (fun s a => stationaryWeight (Icc (l-R) (u+R)) (fun x => (-m:ℝ)*V x)
            (fun x => conj (A₀ a x)) s) n
    simpa only [he,Int.cast_neg] using hs
  · exact exactPassageCoeff_summed_positive hm hH hA hA₀ hAc hAd hsupp hlo huo hlu hR
      hP hV hPV hd hHc hAcont hδt

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unfolded and folded retained densities, branch kernels, residue sampling, and spectral limits. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

lemma circle_integral_lift (o : ℝ) (q : UnitAddCircle → ℝ) :
    (∫ x, circleDensityLift o q x) = ∫ a, q a ∂AddCircle.haarAddCircle := by
  rw [circleDensityLift,integral_indicator measurableSet_Ioc]
  have h := AddCircle.integral_preimage 1 o q
  simpa [AddCircle.volume_eq_smul_haarAddCircle] using h

lemma integrable_circleDensityLift {q : UnitAddCircle → ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (o : ℝ) :
    Integrable (circleDensityLift o q) := by
  have hmp : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc o (o+1))) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 o
  have hi : IntegrableOn (fun x : ℝ => q (x : UnitAddCircle)) (Ioc o (o+1)) :=
    (hmp.integrable_comp hq.aestronglyMeasurable).2 hq
  exact hi.integrable_indicator measurableSet_Ioc

/-- Lifting a circle density on one period commutes with every measurable
spectral pushforward. This includes the actual jitter, not just polynomial tests. -/
lemma circleDensityLift_pushforward {Y : Type*} [MeasurableSpace Y]
    {q : UnitAddCircle → ℝ} (hq : Integrable q AddCircle.haarAddCircle)
    {T : UnitAddCircle → Y} (hT : Measurable T) (o : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (circleDensityLift o q)).map
      (fun x : ℝ => T (x : UnitAddCircle)) =
    (AddCircle.haarAddCircle.withDensityᵥ q).map T := by
  have hTm : Measurable (fun x : ℝ => T (x : UnitAddCircle)) := hT.comp AddCircle.measurable_mk'
  ext s hs
  rw [VectorMeasure.map_apply _ hTm hs,VectorMeasure.map_apply _ hT hs,
    withDensityᵥ_apply (integrable_circleDensityLift hq o) (hTm hs),
    withDensityᵥ_apply hq (hT hs)]
  rw [← integral_indicator (hTm hs),← integral_indicator (hT hs)]
  rw [← circle_integral_lift o ((T ⁻¹' s).indicator q)]
  congr 1
  funext x
  by_cases hx : x ∈ Ioc o (o+1) <;> by_cases hxs : T (x : UnitAddCircle) ∈ s <;>
    simp [circleDensityLift,hx,hxs]

lemma circleDensityLift_eq {q : UnitAddCircle → ℝ} {q₀ : ℝ → ℝ} {o : ℝ}
    (he : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hs : Function.support q₀ ⊆ Ioc o (o+1)) : circleDensityLift o q = q₀ := by
  funext x
  by_cases hx : x ∈ Ioc o (o+1)
  · simp [circleDensityLift,hx,he x hx]
  · have hzero : q₀ x = 0 := by by_contra hn; exact hx (hs hn)
    simp [circleDensityLift,hx,hzero]

lemma integrable_branchDensity {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : IntegrableOn q I) : Integrable (branchDensity I J g D q) := by
  have he : IntegrableOn (branchDensity I J g D q) (J '' I) := by
    rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hI hJ hinj]
    apply hq.congr (ae_restrict_of_forall_mem hI (fun x hx => ?_))
    rw [smul_eq_mul,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  have hs : (J '' I).indicator (branchDensity I J g D q) = branchDensity I J g D q := by
    funext y
    by_cases hy : y ∈ J '' I
    · exact indicator_of_mem hy _
    · simp [hy,branchDensity]
  simpa only [hs] using he.integrable_indicator himage

/-- Exact pushforward of the old squared coefficient on a branch. The only
inverse assumptions are the ordinary left-inverse identities on that branch. -/
lemma branchDensity_pushforward {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I)) (hJm : Measurable J)
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q) (hqs : Function.support q ⊆ I) :
    ((volume : Measure ℝ).withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J g D q) := by
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hq.integrableOn
  ext s hs
  rw [VectorMeasure.map_apply _ hJm hs,withDensityᵥ_apply hq (hJm hs),withDensityᵥ_apply hK hs]
  rw [← integral_indicator (hJm hs),← integral_indicator hs]
  have hleft : (∫ x, (J ⁻¹' s).indicator q x) = ∫ x in I, (J ⁻¹' s).indicator q x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hqx : q x = 0 := by
      by_contra hh
      exact hx (hqs hh)
    by_cases hxs : x ∈ J ⁻¹' s <;> simp [hxs,hqx]
  have hright : (∫ y, s.indicator (branchDensity I J g D q) y) =
      ∫ y in J '' I, s.indicator (branchDensity I J g D q) y := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_cases hys : y ∈ s <;> simp [hys,branchDensity,hy]
  rw [hleft,hright,integral_image_eq_integral_abs_deriv_smul hI hJ hinj]
  apply setIntegral_congr_fun hI
  intro x hx
  dsimp only
  rw [smul_eq_mul]
  by_cases hxs : J x ∈ s
  · rw [indicator_of_mem (show x ∈ J ⁻¹' s from hxs),indicator_of_mem hxs,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  · rw [indicator_of_notMem (show x ∉ J ⁻¹' s from hxs),indicator_of_notMem hxs,mul_zero]

lemma density_map_congr_support {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {T₁ T₂ : X → Y} (h₁ : Measurable T₁) (h₂ : Measurable T₂)
    (he : ∀ x, f x ≠ 0 → T₁ x = T₂ x) :
    (μ.withDensityᵥ f).map T₁ = (μ.withDensityᵥ f).map T₂ := by
  classical
  ext s hs
  rw [VectorMeasure.map_apply _ h₁ hs,VectorMeasure.map_apply _ h₂ hs,
    withDensityᵥ_apply hf (h₁ hs),withDensityᵥ_apply hf (h₂ hs),
    ← integral_indicator (h₁ hs),← integral_indicator (h₂ hs)]
  congr 1
  funext x
  change (if T₁ x ∈ s then f x else 0) = (if T₂ x ∈ s then f x else 0)
  by_cases hx : f x = 0
  · simp [hx]
  · rw [he x hx]

/-- The branch-Jacobian formula on the actual circle. The global periodic
jitter need not be injective; only the good arc bearing the weight is used. -/
lemma circle_branch_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J₀ g D q₀) := by
  have hlift := circleDensityLift_eq hq₀ hq₀s
  have hi : Integrable q₀ := by rw [← hlift]; exact integrable_circleDensityLift hq o
  rw [← circleDensityLift_pushforward hq hj o,hlift]
  rw [density_map_congr_support (T₁ := fun x : ℝ => J (x : UnitAddCircle)) hi (hj.comp AddCircle.measurable_mk') hj₀
    (fun x hx => hJe x (hqs hx))]
  exact branchDensity_pushforward hI himage hj₀ hJ hinj hg hD hi hqs

/-- Total variation contracts under the actual temporal-frequency pushforward.
The real L¹ normalization has no factor 1/2. -/
lemma l1_pushforward_contraction {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → ℝ} {g : Y → ℝ} {T : X → Y}
    (hf : Integrable f μ) (hg : Integrable g ν) (hT : Measurable T)
    (hmap : (μ.withDensityᵥ f).map T = ν.withDensityᵥ g) :
    (∫ y, |g y| ∂ν) ≤ ∫ x, |f x| ∂μ := by
  have hv := MeasureTheory.VectorMeasure.variation_map_le (μ := μ.withDensityᵥ f) (φ := T)
  rw [hmap,Measure.variation_withDensityᵥ hg,Measure.variation_withDensityᵥ hf] at hv
  have hh := hv univ
  rw [Measure.map_apply hT MeasurableSet.univ] at hh
  simp only [preimage_univ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
  have he (z : ℝ) : ‖z‖ₑ = ENNReal.ofReal |z| := Real.enorm_eq_ofReal_abs z
  simp_rw [he] at hh
  rw [← ofReal_integral_eq_lintegral_ofReal hg.abs (Filter.Eventually.of_forall (fun _ => abs_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hf.abs (Filter.Eventually.of_forall (fun _ => abs_nonneg _))] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => abs_nonneg _))).mp hh

lemma l1_pushforward_difference {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f₁ f₂ : X → ℝ} {g₁ g₂ : Y → ℝ} {T : X → Y}
    (hf₁ : Integrable f₁ μ) (hf₂ : Integrable f₂ μ)
    (hg₁ : Integrable g₁ ν) (hg₂ : Integrable g₂ ν) (hT : Measurable T)
    (h₁ : (μ.withDensityᵥ f₁).map T = ν.withDensityᵥ g₁)
    (h₂ : (μ.withDensityᵥ f₂).map T = ν.withDensityᵥ g₂) :
    (∫ y, |g₁ y-g₂ y| ∂ν) ≤ ∫ x, |f₁ x-f₂ x| ∂μ := by
  apply l1_pushforward_contraction (hf₁.sub hf₂) (hg₁.sub hg₂) hT
  rw [withDensityᵥ_sub hf₁ hf₂,withDensityᵥ_sub hg₁ hg₂]
  have he := map_sub (MeasureTheory.VectorMeasure.mapGm T) (μ.withDensityᵥ f₁) (μ.withDensityᵥ f₂)
  change (μ.withDensityᵥ f₁-μ.withDensityᵥ f₂).map T =
    (μ.withDensityᵥ f₁).map T-(μ.withDensityᵥ f₂).map T at he
  rw [he,h₁,h₂]

/-- Exact Jacobian cancellation in the unfolded output frequency t=(j+y)/N. -/
lemma temporalFrequency_pushforward {q : ℝ → ℝ} (hq : Integrable q)
    {n : ℝ} (hn : 0 < n) (j : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (fun y => n⁻¹*q y)).map (fun y => (j+y)/n) =
      (volume : Measure ℝ).withDensityᵥ (fun t => q (n*t-j)) := by
  have hmap : Measurable (fun y : ℝ => (j+y)/n) := by fun_prop
  have hq' : Integrable (fun t => q (n*t-j)) := by
    simpa only [sub_eq_add_neg] using
      (integrable_comp_mul_left_iff (fun x => q (x+ -j)) hn.ne').2 (hq.comp_add_right (-j))
  ext s hs
  rw [VectorMeasure.map_apply _ hmap hs,withDensityᵥ_apply (hq.const_mul n⁻¹) (hmap hs),
    withDensityᵥ_apply hq' hs,integral_const_mul]
  let F : ℝ → ℝ := ((fun y : ℝ => (j+y)/n) ⁻¹' s).indicator q
  have he : (fun t => F (n*t-j)) = s.indicator (fun t => q (n*t-j)) := by
    funext t
    by_cases ht : t ∈ s <;> simp [F,ht,hn.ne']
  rw [← integral_indicator (hmap hs),← integral_indicator hs,← he]
  change n⁻¹*(∫ y, F y) = ∫ t, F (n*t-j)
  rw [Measure.integral_comp_mul_left (fun x => F (x-j)) n,integral_sub_right_eq_self]
  simp only [smul_eq_mul,abs_of_pos (inv_pos.mpr hn)]

/-- Pushforward through a fixed smooth jitter followed by the output affine frequency.
This is the exact (not weak or asymptotic) density appearing in the passage. -/
lemma temporalFrequency_pushforward_comp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {W : X → ℝ} {q : ℝ → ℝ} {J : X → ℝ}
    (hW : Integrable W μ) (hq : Integrable q) (hJ : Measurable J)
    (hpush : (μ.withDensityᵥ W).map J = (volume : Measure ℝ).withDensityᵥ q)
    {n : ℝ} (hn : 0 < n) (j : ℝ) :
    (μ.withDensityᵥ (fun a => n⁻¹*W a)).map (fun a => (j+J a)/n) =
      (volume : Measure ℝ).withDensityᵥ (fun t => q (n*t-j)) := by
  have haf : Measurable (fun y : ℝ => (j+y)/n) := by fun_prop
  have hcomp (v : VectorMeasure X ℝ) :
      v.map (fun a => (j+J a)/n) = (v.map J).map (fun y : ℝ => (j+y)/n) := by
    ext s hs
    have hcompm : Measurable (fun a => (j+J a)/n) := haf.comp hJ
    rw [VectorMeasure.map_apply _ hcompm hs,
      VectorMeasure.map_apply _ haf hs,VectorMeasure.map_apply _ hJ (haf hs)]
    rfl
  rw [hcomp]
  have he : μ.withDensityᵥ (fun a => n⁻¹*W a) = n⁻¹ • μ.withDensityᵥ W := by
    ext s hs
    rw [withDensityᵥ_apply (hW.const_mul _) hs,smul_apply,withDensityᵥ_apply hW hs,
      integral_const_mul,smul_eq_mul]
  have heq : (volume : Measure ℝ).withDensityᵥ (fun y => n⁻¹*q y) =
      n⁻¹ • (volume : Measure ℝ).withDensityᵥ q := by
    ext s hs
    rw [withDensityᵥ_apply (hq.const_mul _) hs,smul_apply,withDensityᵥ_apply hq hs,
      integral_const_mul,smul_eq_mul]
  rw [he,VectorMeasure.map_smul,hpush,← heq]
  exact temporalFrequency_pushforward hq hn j

lemma scaledBranchKernel_eq {I : Set ℝ} (J g D q : ℝ → ℝ) {s : ℝ} (hs : s ≠ 0) (y : ℝ) :
    branchDensity I (fun x => s*J x) (fun y => g (y/s)) (fun x => s*D x) q y =
      scaledBranchKernel I J g D q s y := by
  classical
  have he : y ∈ (fun x => s*J x) '' I ↔ y/s ∈ J '' I := by
    constructor
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x,hx,by rw [← hxy]; field_simp⟩
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x,hx,by change s*J x = y; rw [hxy]; field_simp⟩
  by_cases hy : y/s ∈ J '' I
  · simp only [branchDensity,scaledBranchKernel,indicator_of_mem hy,
      indicator_of_mem (he.mpr hy),abs_mul]
    ring
  · simp only [branchDensity,scaledBranchKernel,indicator_of_notMem hy,
      indicator_of_notMem (fun h => hy (he.mp h)),mul_zero]

lemma integrable_scaledBranchKernel {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : Integrable (branchDensity I J g D q)) {s : ℝ} (hs : s ≠ 0) :
    Integrable (scaledBranchKernel I J g D q s) :=
  ((integrable_comp_div_iff _ hs).2 hq).const_mul _

/-- The exact branch kernel in the new temporal coordinate, on the torus.
Only the good arc need be injective, as in the geometric passage. -/
lemma circle_mode_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    {s n : ℝ} (hs : s ≠ 0) (hn : 0 < n) (j : ℝ) :
    (AddCircle.haarAddCircle.withDensityᵥ (fun a => n⁻¹*q a)).map
        (fun a => (j+s*J a)/n) =
      (volume : Measure ℝ).withDensityᵥ
        (fun t => scaledBranchKernel I J₀ g D q₀ s (n*t-j)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hqi.integrableOn
  have hsim : MeasurableSet ((fun x => s*J₀ x) '' I) := by
    have he : (fun x => s*J₀ x) '' I = (fun y : ℝ => s*y) '' (J₀ '' I) := by
      rw [image_image]
    rw [he]
    exact (Homeomorph.mulLeft₀ s hs).measurableEmbedding.measurableSet_image.mpr himage
  have hp := circle_branch_pushforward (g := fun y => g (y/s)) hq hq₀ hq₀s hqs
    (measurable_const.mul hj) (measurable_const.mul hj₀)
    (fun x hx => congrArg (fun y => s*y) (hJe x hx)) hI hsim
    (fun x hx => (hJ x hx).const_mul s)
    (fun x hx y hy he => hinj hx hy (mul_left_cancel₀ hs he))
    (fun x hx => show g (s*J₀ x/s) = x by simpa [hs] using hg x hx)
    (fun x hx => mul_ne_zero hs (hD x hx))
  have he : branchDensity I (fun x => s*J₀ x) (fun y => g (y/s)) (fun x => s*D x) q₀ =
      scaledBranchKernel I J₀ g D q₀ s := funext (scaledBranchKernel_eq _ _ _ _ hs)
  change (AddCircle.haarAddCircle.withDensityᵥ q).map (fun a => s*J a) =
    (volume : Measure ℝ).withDensityᵥ
      (branchDensity I (fun x => s*J₀ x) (fun y => g (y/s)) (fun x => s*D x) q₀) at hp
  rw [he] at hp
  exact temporalFrequency_pushforward_comp hq (integrable_scaledBranchKernel hK hs)
    (measurable_const.mul hj) hp hn j

lemma integral_abs_finset_sum_le {Y ι : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (S : Finset ι) {f : ι → Y → ℝ} (hf : ∀ i ∈ S, Integrable (f i) ν) :
    (∫ y, |∑ i ∈ S, f i y| ∂ν) ≤ ∑ i ∈ S, ∫ y, |f i y| ∂ν := by
  calc
    _ ≤ ∫ y, ∑ i ∈ S, |f i y| ∂ν := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => abs_nonneg _)
      · exact integrable_finsetSum _ (fun i hi => (hf i hi).abs)
      · exact Filter.Eventually.of_forall (fun y => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := integral_finsetSum _ (fun i hi => (hf i hi).abs)

/-- Summed coefficient mass error controls the full density error, not merely
its moments. The maps may vary with the angular index. -/
lemma finite_density_sum_error {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {q w : ι → X → ℝ} {g h : ι → Y → ℝ}
    {T : ι → X → Y} (S : Finset ι)
    (hq : ∀ i ∈ S, Integrable (q i) μ) (hw : ∀ i ∈ S, Integrable (w i) μ)
    (hg : ∀ i ∈ S, Integrable (g i) ν) (hh : ∀ i ∈ S, Integrable (h i) ν)
    (hT : ∀ i ∈ S, Measurable (T i))
    (hqp : ∀ i ∈ S, (μ.withDensityᵥ (q i)).map (T i) = ν.withDensityᵥ (g i))
    (hwp : ∀ i ∈ S, (μ.withDensityᵥ (w i)).map (T i) = ν.withDensityᵥ (h i)) :
    (∫ y, |(∑ i ∈ S, g i y)-(∑ i ∈ S, h i y)| ∂ν) ≤
      ∑ i ∈ S, ∫ x, |q i x-w i x| ∂μ := by
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, ∫ y, |g i y-h i y| ∂ν :=
      integral_abs_finset_sum_le S (fun i hi => (hg i hi).sub (hh i hi))
    _ ≤ _ := Finset.sum_le_sum (fun i hi =>
      l1_pushforward_difference (hq i hi) (hw i hi) (hg i hi) (hh i hi)
        (hT i hi) (hqp i hi) (hwp i hi))

lemma cutoff_mass_pointwise {q w χ ψ : ℝ} (hq : 0 ≤ q)
    (hχ : 0 ≤ χ ∧ χ ≤ 1) (hχw : w ≠ 0 → χ = 1)
    (hψ : 0 ≤ ψ ∧ ψ ≤ 1) :
    |ψ^2*χ^2*q-ψ^2*w| ≤ |q-w| := by
  have hχ2 : χ^2 ≤ 1 := by nlinarith [hχ.1,hχ.2]
  have hψ2 : ψ^2 ≤ 1 := by nlinarith [hψ.1,hψ.2]
  have hh : |χ^2*q-w| ≤ |q-w| := by
    by_cases hw : w = 0
    · rw [hw,sub_zero,sub_zero,abs_of_nonneg hq,abs_of_nonneg (mul_nonneg (sq_nonneg _) hq)]
      exact mul_le_of_le_one_left hq hχ2
    · simp [hχw hw]
  calc
    _ = ψ^2*|χ^2*q-w| := by rw [mul_assoc,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg _)]
    _ ≤ |χ^2*q-w| := mul_le_of_le_one_left (abs_nonneg _) hψ2
    _ ≤ _ := hh

lemma integrable_unfoldedModeDensity {I : Set ℝ} {J g D q₀ : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q₀) {n j : ℝ} (hn : 0 < n) (hj : j ≠ 0) :
    Integrable (unfoldedModeDensity I J g D q₀ n j) := by
  have hi := integrable_scaledBranchKernel
    (integrable_branchDensity hI himage hJ hinj hg hD (hq.const_mul n).integrableOn)
    (div_ne_zero hj hn.ne')
  change Integrable (fun t => scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (n*t-j))
  simpa only [sub_eq_add_neg] using
    (integrable_comp_mul_left_iff (fun x =>
      scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (x+ -j)) hn.ne').2
      (hi.comp_add_right (-j))

/-- Exact density of an actual circle mode before any stationary approximation. -/
lemma unfoldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map
        (fun a => (j+(j/n)*J a)/n) =
      (volume : Measure ℝ).withDensityᵥ (unfoldedModeDensity I J₀ g D q₀ n j) := by
  have hsupp (L : Set ℝ) (hh : Function.support q₀ ⊆ L) :
      Function.support (fun a => n*q₀ a) ⊆ L := by
    intro x hx
    apply hh
    intro hz
    exact hx (by simp only [hz,mul_zero])
  have hp := circle_mode_pushforward (q := fun a => n*q a) (q₀ := fun a => n*q₀ a)
    (s := j/n) (hq.const_mul n) (fun x hx => congrArg (fun y => n*y) (hq₀ x hx))
    (hsupp _ hq₀s) (hsupp _ hqs) hj hj₀ hJe hI himage hJ hinj hg hD
    (div_ne_zero hjn hn.ne') hn j
  change _ = (volume : Measure ℝ).withDensityᵥ
    (fun t => scaledBranchKernel I J₀ g D (fun a => n*q₀ a) (j/n) (n*t-j))
  simpa only [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul] using hp

end ThreeTorus

noncomputable section
open Set Function Filter
open scoped Topology NNReal
namespace ThreeTorus

lemma support_branchKernel_subset {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ} :
    support (branchKernel I J F) ⊆ (fun p : ℝ × ℝ => (J p.1,p.2)) '' tsupport F := by
  rintro ⟨s,a⟩ hh
  have hs : s ∈ J '' I := by
    by_contra hn
    exact hh (by simp [branchKernel,hn])
  have hp := invFunOn_pos hs
  refine ⟨(invFunOn J I s,a),subset_tsupport F ?_,?_⟩
  · intro hz
    exact hh (by simp [branchKernel,hs,hz])
  · simp only [hp.2]

lemma branchKernel_compact {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) : HasCompactSupport (branchKernel I J F) := by
  apply HasCompactSupport.intro (hc.image (by fun_prop : Continuous (fun p : ℝ × ℝ => (J p.1,p.2))))
  intro p hp
  by_contra hn
  exact hp (support_branchKernel_subset hn)

lemma branchKernel_smooth {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (branchKernel I J F) := by
  classical
  let g := invFunOn J I
  let M := (fun p : ℝ × ℝ => (J p.1,p.2)) '' tsupport F
  have hM : IsCompact M := hc.image (by fun_prop)
  have hzero {p : ℝ × ℝ} (hp : p ∉ M) : branchKernel I J F p = 0 :=
    notMem_support.mp (fun hn => hp (support_branchKernel_subset hn))
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := by
    exact hJ.deriv' 
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ M
  · rcases hp with ⟨⟨x,a⟩,hx,rfl⟩
    have hxI : x ∈ I := (hs hx).1
    have hy : J x ∈ J '' I := mem_image_of_mem J hxI
    have hgi := contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)
    have hge : g (J x) = x := by
      exact hinj (invFunOn_pos hy).1 hxI (invFunOn_pos hy).2
    have hin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (g p.1,p.2)) (J x,a) :=
      (hgi.comp (J x,a) contDiffAt_fst).prodMk contDiffAt_snd
    have hDen : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => |deriv J (g p.1)|) (J x,a) := by
      have hh : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × ℝ => deriv J (g p.1)) (J x,a) :=
        hD.contDiffAt.comp (J x,a) (hgi.comp (J x,a) contDiffAt_fst)
      exact (contDiffAt_abs (by simpa only [hge] using hd x hxI)).comp (J x,a) hh
    have hquot : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => F (g p.1,p.2) / |deriv J (g p.1)|) (J x,a) := by
      apply (hF.contDiffAt.comp _ hin).div hDen
      simpa only [hge] using abs_ne_zero.mpr (hd x hxI)
    apply hquot.congr_of_eventuallyEq
    have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 (J x,a), p.1 ∈ J '' I :=
      continuous_fst.continuousAt.eventually ((isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hy)
    filter_upwards [hnear] with p hp
    simp only [branchKernel,ite_eq_left hp,g]
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hzero hq

lemma branchKernel_bounds {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      (∀ s a, A < |s| → branchKernel I J F (s,a) = 0) ∧
      (∀ s a, D < |a| → branchKernel I J F (s,a) = 0) := by
  have hC := branchKernel_compact (I := I) hJ hc
  obtain ⟨R,hR⟩ := hC.isBounded.subset_closedBall (0 : ℝ × ℝ)
  refine ⟨max R 0,max R 0,le_max_right _ _,le_max_right _ _,?_,?_⟩
  · intro s a hs
    by_contra hn
    have hh := hR (subset_tsupport _ hn)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] at hh
    have hab : |s| ≤ R := by simpa only [Real.norm_eq_abs] using (le_max_left ‖s‖ ‖a‖).trans hh
    exact (not_lt_of_ge (hab.trans (le_max_left _ _))) hs
  · intro s a hs
    by_contra hn
    have hh := hR (subset_tsupport _ hn)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] at hh
    have hab : |a| ≤ R := by simpa only [Real.norm_eq_abs] using (le_max_right ‖s‖ ‖a‖).trans hh
    exact (not_lt_of_ge (hab.trans (le_max_left _ _))) hs

lemma affineKernel_eq_zero_s {F : ℝ × ℝ → ℝ} {L β A s y : ℝ}
    (hF : ∀ s a, A < |s| → F (s,a) = 0) (hs : A < |s|) :
    affineKernel F L β s y = 0 := by simp [affineKernel,hF _ _ hs]

lemma affineKernel_eq_zero_y {F : ℝ × ℝ → ℝ} {L β A D s y : ℝ}
    (hL : 0 < L) (_hA : 0 ≤ A) (hD : 0 ≤ D)
    (hFs : ∀ s a, A < |s| → F (s,a) = 0)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0)
    (hy : A*(L*D+|β|) < |y|) : affineKernel F L β s y = 0 := by
  by_cases hs : s = 0
  · simp [affineKernel,hs]
  by_cases hsA : A < |s|
  · exact affineKernel_eq_zero_s hFs hsA
  have hsA' : |s| ≤ A := le_of_not_gt hsA
  have hh : D < |(y/s-β)/L| := by
    by_contra hn
    have hn' := le_of_not_gt hn
    rw [abs_div,abs_of_pos hL,div_le_iff₀ hL] at hn'
    have hb := abs_add_le (y/s-β) β
    rw [sub_add_cancel] at hb
    have hx : |y/s| ≤ L*D+|β| := by linarith
    rw [abs_div,div_le_iff₀ (abs_pos.mpr hs)] at hx
    have hright : (L*D+|β|)*|s| ≤ (L*D+|β|)*A :=
      mul_le_mul_of_nonneg_left hsA' (by positivity)
    nlinarith
  simp [affineKernel,hFa _ _ hh]

lemma affineKernel_hasCompactSupport {F : ℝ × ℝ → ℝ} {L β A D : ℝ}
    (hL : 0 < L) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hFs : ∀ s a, A < |s| → F (s,a) = 0)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0) :
    HasCompactSupport (Function.uncurry (affineKernel F L β)) := by
  apply HasCompactSupport.intro
    ((isCompact_Icc (a := -A) (b := A)).prod
      (isCompact_Icc (a := -(A*(L*D+|β|))) (b := A*(L*D+|β|))))
  rintro ⟨s,y⟩ hp
  simp only [mem_prod,mem_Icc,← abs_le,not_and_or,not_le] at hp
  rcases hp with hs | hy
  · exact affineKernel_eq_zero_s hFs hs
  · exact affineKernel_eq_zero_y hL hA hD hFs hFa hy

lemma affineKernel_smooth {F : ℝ × ℝ → ℝ} {L β ε : ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hε : 0 < ε)
    (hz : ∀ s a, |s| < ε → F (s,a) = 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (affineKernel F L β)) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨s,y⟩
  by_cases hs : s = 0
  · have he : ∀ᶠ p : ℝ × ℝ in 𝓝 (s,y), |p.1| < ε := by
      have hc : Continuous (fun p : ℝ × ℝ => |p.1|) := by fun_prop
      apply hc.continuousAt.eventually (gt_mem_nhds ?_)
      simpa [hs] using hε
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with p hp
    simp [Function.uncurry,affineKernel,hz _ _ hp]
  · have ha : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => |p.1|) (s,y) := by
      exact (contDiffAt_abs hs).comp (s,y) contDiffAt_fst
    have hin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (p.1,(p.2/p.1-β)/L)) (s,y) := by
      exact contDiffAt_fst.prodMk (((contDiffAt_snd.div contDiffAt_fst hs).sub contDiffAt_const).div_const L)
    by_cases hL : L = 0
    · have he : Function.uncurry (affineKernel F L β) = fun _ => (0:ℝ) := by
        funext p; simp [Function.uncurry,affineKernel,hL]
      rw [he]
      exact contDiffAt_const
    · exact ((ha.mul contDiffAt_const).inv (mul_ne_zero (abs_ne_zero.mpr hs) hL)).mul
        (hF.contDiffAt.comp (s,y) hin)

/-- A compact smooth kernel has a single global Lipschitz bound. -/
lemma compact_smooth_lipschitz {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hc : HasCompactSupport F) : ∃ C : ℝ≥0, LipschitzWith C F := by
  obtain ⟨C,hC⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hF.continuous_fderiv (by simp))
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by simp))
  intro p
  exact (hC p).trans (le_max_left _ _)

lemma compact_smooth_kernel_lipschitz {K : ℝ → ℝ → ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry K))
    (hc : HasCompactSupport (Function.uncurry K)) :
    ∃ C : ℝ≥0, ∀ y, LipschitzWith C (fun s => K s y) := by
  obtain ⟨C,hC⟩ := compact_smooth_lipschitz hK hc
  refine ⟨C, fun y => ?_⟩
  have hp : LipschitzWith 1 (fun s : ℝ => (s,y)) := by
    simpa using (LipschitzWith.id.prodMk (LipschitzWith.const y))
  simpa only [mul_one, Function.comp_def, Function.uncurry] using hC.comp hp

end ThreeTorus
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace ThreeTorus

private lemma mem_samplingWindow {x : ℝ} {M : ℕ} {j : ℤ}
    (hj : |x-j| ≤ M) : j ∈ samplingWindow x M := by
  have hf := Int.floor_le x
  have hf' := Int.lt_floor_add_one x
  have ha := abs_le.mp hj
  simp only [samplingWindow, Finset.mem_Icc]
  constructor
  · have : (⌊x⌋:ℝ)-(M:ℝ)-1 ≤ j := by linarith
    exact_mod_cast this
  · have : (j:ℝ) ≤ (⌊x⌋:ℝ)+(M:ℝ)+1 := by linarith
    exact_mod_cast this

private lemma samplingWindow_card (x : ℝ) (M : ℕ) :
    (samplingWindow x M).card = 2*M+3 := by
  rw [samplingWindow, Int.card_Icc]
  have he : ⌊x⌋+(M:ℤ)+1+1-(⌊x⌋-(M:ℤ)-1) = ((2*M+3:ℕ):ℤ) := by push_cast; ring
  rw [he, Int.toNat_natCast]

end ThreeTorus

namespace ThreeTorus

lemma residue_window_mem {P M n : ℕ} {h k : ℤ} {t : ℝ}
    (hP : 0 < P) (hy : |(n:ℝ)*t-h-k*P| ≤ M) :
    k ∈ samplingWindow (((n:ℝ)*t-h)/P) M := by
  have hP' : (0:ℝ) < P := by exact_mod_cast hP
  have hP1 : (1:ℝ) ≤ P := by exact_mod_cast hP
  apply mem_samplingWindow
  rw [show ((n:ℝ)*t-h)/P-k = ((n:ℝ)*t-h-k*P)/P by field_simp,
    abs_div,abs_of_pos hP']
  apply (div_le_iff₀ hP').mpr
  exact hy.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) M])

lemma sampledResidueKernel_error {K : ℝ → ℝ → ℝ} {C : ℝ≥0} {P M n : ℕ} {h : ℤ}
    (hK : ∀ y, LipschitzWith C (fun s => K s y))
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0)
    (hP : 0 < P) (hn : 0 < n) (t : ℝ) :
    |sampledResidueKernel K P h n t-fineResidueKernel K P h n t| ≤
      (2*(M:ℝ)+3)*C*M/n := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  let S := samplingWindow (((n:ℝ)*t-h)/P) M
  have hc (k : ℤ) (hk : k ∉ S) : (M:ℝ) < |(n:ℝ)*t-h-k*P| := by
    by_contra hh
    exact hk (residue_window_mem hP (not_lt.mp hh))
  have hs : sampledResidueKernel K P h n t =
      ∑ k ∈ S, K (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) ((n:ℝ)*t-h-k*P) :=
    tsum_eq_sum (fun k hk => hKy _ _ (hc k hk))
  have hf : fineResidueKernel K P h n t =
      ∑ k ∈ S, K t ((n:ℝ)*t-h-k*P) :=
    tsum_eq_sum (fun k hk => hKy _ _ (hc k hk))
  rw [hs,hf,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ S, |K (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) ((n:ℝ)*t-h-k*P)-
      K t ((n:ℝ)*t-h-k*P)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ S, (C:ℝ)*M/n := by
      apply Finset.sum_le_sum
      intro k _hk
      by_cases hk : |(n:ℝ)*t-h-k*P| ≤ M
      · have hd : |((h:ℝ)+(k:ℝ)*P)/(n:ℝ)-t| ≤ (M:ℝ)/n := by
          rw [show ((h:ℝ)+(k:ℝ)*P)/(n:ℝ)-t = -((n:ℝ)*t-h-k*P)/n by field_simp; ring,
            abs_div,abs_neg,abs_of_pos hn']
          exact div_le_div_of_nonneg_right hk hn'.le
        calc
          _ ≤ (C:ℝ)*|((h:ℝ)+(k:ℝ)*P)/n-t| := by
            simpa only [Real.dist_eq] using (hK ((n:ℝ)*t-h-k*P)).dist_le_mul (((h:ℝ)+(k:ℝ)*P)/n) t
          _ ≤ (C:ℝ)*((M:ℝ)/n) := mul_le_mul_of_nonneg_left hd C.coe_nonneg
          _ = _ := by ring
      · rw [hKy _ _ (lt_of_not_ge hk),hKy _ _ (lt_of_not_ge hk),sub_self,abs_zero]
        positivity
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,samplingWindow_card]; push_cast; ring

lemma fineResidueKernel_eq_zero {K : ℝ → ℝ → ℝ} {A t : ℝ}
    (hKs : ∀ s y, A < |s| → K s y = 0) (ht : A < |t|) (P n : ℕ) (h : ℤ) :
    fineResidueKernel K P h n t = 0 := by
  unfold fineResidueKernel
  simp only [hKs _ _ ht,tsum_zero]

lemma sampledResidueKernel_eq_zero {K : ℝ → ℝ → ℝ} {A t : ℝ} {M n : ℕ}
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0)
    (hn : 0 < n) (ht : A+M < |t|) (P : ℕ) (h : ℤ) :
    sampledResidueKernel K P h n t = 0 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  unfold sampledResidueKernel
  suffices he : ∀ k : ℤ, K (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) ((n:ℝ)*t-h-k*P) = 0 by
    simp only [he,tsum_zero]
  intro k
  by_cases hs : A < |((h:ℝ)+(k:ℝ)*P)/(n:ℝ)|
  · exact hKs _ _ hs
  apply hKy
  by_contra hh
  have hk : |(n:ℝ)*t-h-k*P| ≤ M := not_lt.mp hh
  have ht' : |t| ≤ |((h:ℝ)+(k:ℝ)*P)/(n:ℝ)|+|(n:ℝ)*t-h-k*P|/(n:ℝ) := by
    calc
      _ = |((h:ℝ)+(k:ℝ)*P)/(n:ℝ)+((n:ℝ)*t-h-k*P)/(n:ℝ)| := by congr 1; field_simp; ring
      _ ≤ _ := by simpa only [abs_div,abs_of_pos hn'] using
        abs_add_le (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) (((n:ℝ)*t-h-k*P)/(n:ℝ))
  have hdiv : |(n:ℝ)*t-h-k*P|/(n:ℝ) ≤ (M:ℝ) := by
    apply (div_le_iff₀ hn').mpr
    exact hk.trans (by nlinarith)
  linarith [not_lt.mp hs]

end ThreeTorus

namespace ThreeTorus

private lemma residue_abs_bound {P : ℕ} (hP : 0 < P) (h k : ℤ) :
    |(k:ℝ)| ≤ |(h:ℝ)+k*P|+|(h:ℝ)| := by
  have hP1 : (1:ℝ) ≤ P := by exact_mod_cast hP
  calc
    _ ≤ |(k:ℝ)| * P := by nlinarith [abs_nonneg (k:ℝ)]
    _ = |(h:ℝ)+k*P-h| := by rw [show (h:ℝ)+k*P-h = k*P by ring,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ P from Nat.cast_nonneg P)]
    _ ≤ _ := abs_sub _ _

lemma continuous_sampledResidueKernel {K : ℝ → ℝ → ℝ} {A : ℝ} {n P : ℕ} (h : ℤ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0) (hn : 0 < n) (hP : 0 < P) :
    Continuous (sampledResidueKernel K P h n) := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨B,hB⟩ := exists_nat_gt ((n:ℝ)*A+|(h:ℝ)|)
  let S := samplingWindow 0 B
  have he (t : ℝ) : sampledResidueKernel K P h n t =
      ∑ k ∈ S, K (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) ((n:ℝ)*t-h-k*P) := by
    apply tsum_eq_sum
    intro k hk
    apply hKs
    by_contra hh
    have ha : |(h:ℝ)+k*P| ≤ (n:ℝ)*A := by
      have hh' : |(h:ℝ)+k*P|/(n:ℝ) ≤ A := by simpa only [abs_div,abs_of_pos hn'] using not_lt.mp hh
      have := (div_le_iff₀ hn').mp hh'
      nlinarith
    have hk' : |(k:ℝ)| < B := lt_of_le_of_lt (residue_abs_bound hP h k) (by linarith)
    exact hk (mem_samplingWindow (by simpa only [zero_sub,abs_neg] using hk'.le))
  rw [show sampledResidueKernel K P h n = fun t =>
      ∑ k ∈ S, K (((h:ℝ)+(k:ℝ)*P)/(n:ℝ)) ((n:ℝ)*t-h-k*P) from funext he]
  apply continuous_finsetSum
  intro k _
  exact hK.comp (show Continuous (fun t : ℝ => (((h:ℝ)+(k:ℝ)*P)/(n:ℝ), (n:ℝ)*t-h-k*P)) by fun_prop)

lemma continuous_fineResidueKernel {K : ℝ → ℝ → ℝ} {A : ℝ} {M n P : ℕ} (h : ℤ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0) (hP : 0 < P) :
    Continuous (fineResidueKernel K P h n) := by
  classical
  obtain ⟨B,hB⟩ := exists_nat_gt ((n:ℝ)*A+M+|(h:ℝ)|)
  let S := samplingWindow 0 B
  have he (t : ℝ) : fineResidueKernel K P h n t =
      ∑ k ∈ S, K t ((n:ℝ)*t-h-k*P) := by
    apply tsum_eq_sum
    intro k hk
    by_cases hs : A < |t|
    · exact hKs _ _ hs
    apply hKy
    by_contra hh
    have ha : |(h:ℝ)+k*P| ≤ (n:ℝ)*A+M := by
      calc
        _ = |(n:ℝ)*t-((n:ℝ)*t-h-k*P)| := by congr 1; ring
        _ ≤ |(n:ℝ)*t|+|(n:ℝ)*t-h-k*P| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
          exact add_le_add (mul_le_mul_of_nonneg_left (not_lt.mp hs) (Nat.cast_nonneg n)) (not_lt.mp hh)
    have hk' : |(k:ℝ)| < B := lt_of_le_of_lt (residue_abs_bound hP h k) (by linarith)
    exact hk (mem_samplingWindow (by simpa only [zero_sub,abs_neg] using hk'.le))
  rw [show fineResidueKernel K P h n = fun t => ∑ k ∈ S, K t ((n:ℝ)*t-h-k*P) from funext he]
  apply continuous_finsetSum
  intro k _
  exact hK.comp (show Continuous (fun t : ℝ => (t, (n:ℝ)*t-h-k*P)) by fun_prop)

lemma integrable_sampledResidueKernel_error {K : ℝ → ℝ → ℝ} {A : ℝ} {M n P : ℕ} (h : ℤ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0) (hn : 0 < n) (hP : 0 < P) :
    Integrable (fun t => |sampledResidueKernel K P h n t-fineResidueKernel K P h n t|) := by
  apply ((continuous_sampledResidueKernel h hK hKs hn hP).sub
    (continuous_fineResidueKernel h hK hKs hKy hP)).abs.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (-(A+M)) (A+M)) isCompact_Icc
  intro t ht
  have hab : A+M < |t| := lt_of_not_ge (by simpa only [abs_le,mem_Icc,not_and_or] using ht)
  have htA : A < |t| := lt_of_le_of_lt (le_add_of_nonneg_right (Nat.cast_nonneg M)) hab
  change |sampledResidueKernel K P h n t-fineResidueKernel K P h n t| = 0
  rw [sampledResidueKernel_eq_zero hKs hKy hn hab, fineResidueKernel_eq_zero hKs htA,sub_self,abs_zero]

lemma sampledResidueKernel_integral_error {K : ℝ → ℝ → ℝ} {C : ℝ≥0} {A : ℝ} {M n P : ℕ} (h : ℤ)
    (hA : 0 ≤ A) (hK : ∀ y, LipschitzWith C (fun s => K s y))
    (hCont : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0)
    (hn : 0 < n) (hP : 0 < P) :
    (∫ t, |sampledResidueKernel K P h n t-fineResidueKernel K P h n t|) ≤
      (2*(A+M))*((2*(M:ℝ)+3)*C*M/n) := by
  let B := A+M
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi := integrable_sampledResidueKernel_error h hCont hKs hKy hn hP
  have hs : Function.support (fun t => |sampledResidueKernel K P h n t-fineResidueKernel K P h n t|) ⊆ Icc (-B) B := by
    intro t ht
    by_contra hh
    have hab : B < |t| := lt_of_not_ge (by simpa only [abs_le,mem_Icc,not_and_or] using hh)
    have htA : A < |t| := lt_of_le_of_lt (by dsimp [B]; exact le_add_of_nonneg_right (Nat.cast_nonneg M)) hab
    exact ht (by dsimp only; rw [sampledResidueKernel_eq_zero hKs hKy hn hab,
      fineResidueKernel_eq_zero hKs htA,sub_self,abs_zero])
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-B) B)
    (f := fun t => |sampledResidueKernel K P h n t-fineResidueKernel K P h n t|) (fun x hx => by
      by_contra he
      exact hx (hs he))]
  calc
    _ ≤ ∫ _ in Icc (-B) B, (2*(M:ℝ)+3)*C*M/n :=
      setIntegral_mono_on hi.integrableOn (integrableOn_const (by simp)) measurableSet_Icc
        (fun t _ => sampledResidueKernel_error hK hKy hP hn t)
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith : -B ≤ B)]
      simp only [smul_eq_mul]
      dsimp [B]
      ring

lemma tendsto_sampledResidueKernel_error {K : ℝ → ℝ → ℝ} {C : ℝ≥0} {A : ℝ} {M P : ℕ} (h : ℤ)
    (hA : 0 ≤ A) (hK : ∀ y, LipschitzWith C (fun s => K s y))
    (hCont : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0) (hP : 0 < P) :
    Tendsto (fun n : ℕ => ∫ t, |sampledResidueKernel K P h n t-fineResidueKernel K P h n t|) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact sampledResidueKernel_integral_error h hA hK hCont hKs hKy hn hP
  · simpa only [mul_zero] using (tendsto_const_nhds.mul
      (tendsto_const_div_atTop_nhds_zero_nat ((2*(M:ℝ)+3)*C*M)))

end ThreeTorus

namespace ThreeTorus

/-- Fine-density freezing for the actual neutral affine jitter kernel. All
regularity hypotheses are derived from the smooth compact old coefficient. -/
lemma affineKernel_fine_density {F : ℝ × ℝ → ℝ} {L β A D ε : ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hL : 0 < L) (hA : 0 ≤ A) (hD : 0 ≤ D) (hε : 0 < ε)
    (hz : ∀ s a, |s| < ε → F (s,a) = 0)
    (hFs : ∀ s a, A < |s| → F (s,a) = 0)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0)
    {P : ℕ} (hP : 0 < P) (h : ℤ) :
    Tendsto (fun n : ℕ => ∫ t,
      |sampledResidueKernel (affineKernel F L β) P h n t -
        fineResidueKernel (affineKernel F L β) P h n t|) atTop (𝓝 0) := by
  have hSm := affineKernel_smooth (L := L) (β := β) hF hε hz
  have hCp := affineKernel_hasCompactSupport (β := β) hL hA hD hFs hFa
  obtain ⟨C,hC⟩ := compact_smooth_kernel_lipschitz hSm hCp
  obtain ⟨M,hM⟩ := exists_nat_ge (A*(L*D+|β|))
  apply tendsto_sampledResidueKernel_error h hA hC hSm.continuous
    (fun s y hs => affineKernel_eq_zero_s hFs hs) (M := M) _ hP
  intro s y hy
  exact affineKernel_eq_zero_y hL hA hD hFs hFa (lt_of_le_of_lt hM hy)

lemma passageBranchKernel_formula (I : Set ℝ) (J : ℝ → ℝ) (F : ℝ × ℝ → ℝ) (s y : ℝ) :
    passageBranchKernel I J F s y = |s|⁻¹*branchKernel I J F (y/s,s) := by
  simp [passageBranchKernel,affineKernel]

/-- Fine temporal sampling on any smooth monotone good arc, both signs,
all residue classes and all positive passage integers; no divisibility pin. -/
lemma passageBranchKernel_fine_density {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ a s, |s| < ε → F (a,s) = 0) {P : ℕ} (hP : 0 < P) (h : ℤ) :
    Tendsto (fun n : ℕ => ∫ t,
      |sampledResidueKernel (passageBranchKernel I J F) P h n t-
        fineResidueKernel (passageBranchKernel I J F) P h n t|) atTop (𝓝 0) := by
  have hSm := branchKernel_smooth hJ hIo hinj hd hF hc hs
  obtain ⟨D,A,hD,hA,hx,ha⟩ := branchKernel_bounds (I := I) hJ.continuous hc
  apply affineKernel_fine_density (hSm.comp (contDiff_snd.prodMk contDiff_fst)) (by norm_num) hA hD hε _
    (fun s a hs => ha a s hs) (fun s a hs => hx a s hs) hP h
  intro s a hs
  change branchKernel I J F (a,s) = 0
  simp [branchKernel,hz _ _ hs]

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

/-- The exact sampled leading density is the good-arc Jacobian kernel.
This identifies the coefficient-level approximation with the fine-density
calculation; it is an equality, not a new spectral hypothesis. -/
lemma unfoldedModeDensity_stationary (I : Set ℝ) (J : ℝ → ℝ)
    (F : ℝ × ℝ → ℝ) {n : ℝ} (hn : n ≠ 0) (j t : ℝ) :
    unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (fun a => n⁻¹*F (a,j/n)) n j t =
      passageBranchKernel I J F (j/n) (n*t-j) := by
  classical
  rw [passageBranchKernel_formula]
  unfold unfoldedModeDensity scaledBranchKernel branchDensity branchKernel
  by_cases hy : (n*t-j)/(j/n) ∈ J '' I
  · simp only [hy, ite_eq_left, indicator_of_mem, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  · simp [hy]

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma finite_unfolded_index_error {ι : Type*} {I : Set ℝ} {J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o n : ℝ} (hn : 0 < n)
    (S : Finset ι) (index : ι → ℤ) (hS : ∀ i ∈ S, index i ≠ 0)
    {q w : ι → UnitAddCircle → ℝ} {q₀ w₀ : ι → ℝ → ℝ}
    (hq : ∀ i ∈ S, Integrable (q i) AddCircle.haarAddCircle)
    (hw : ∀ i ∈ S, Integrable (w i) AddCircle.haarAddCircle)
    (hq₀ : ∀ i ∈ S, ∀ x ∈ Ioc o (o+1), q i (x : UnitAddCircle) = q₀ i x)
    (hw₀ : ∀ i ∈ S, ∀ x ∈ Ioc o (o+1), w i (x : UnitAddCircle) = w₀ i x)
    (hqs : ∀ i ∈ S, Function.support (q₀ i) ⊆ Ioc o (o+1) ∩ I)
    (hws : ∀ i ∈ S, Function.support (w₀ i) ⊆ Ioc o (o+1) ∩ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0) :
    (∫ t, |(∑ i ∈ S, unfoldedModeDensity I J₀ g D (q₀ i) n (index i) t)-
      (∑ i ∈ S, unfoldedModeDensity I J₀ g D (w₀ i) n (index i) t)|) ≤
       ∑ i ∈ S, ∫ a, |q i a-w i a| ∂AddCircle.haarAddCircle := by
  have hqI (i : ι) (his : i ∈ S) : Integrable (q₀ i) := by
    rw [← circleDensityLift_eq (hq₀ i his) ((hqs i his).trans inter_subset_left)]
    exact integrable_circleDensityLift (hq i his) o
  have hwI (i : ι) (his : i ∈ S) : Integrable (w₀ i) := by
    rw [← circleDensityLift_eq (hw₀ i his) ((hws i his).trans inter_subset_left)]
    exact integrable_circleDensityLift (hw i his) o
  have hjn (i : ι) (his : i ∈ S) : (index i:ℝ) ≠ 0 := by exact_mod_cast hS i his
  apply finite_density_sum_error
    (g := fun i => unfoldedModeDensity I J₀ g D (q₀ i) n (index i))
    (h := fun i => unfoldedModeDensity I J₀ g D (w₀ i) n (index i)) S hq hw
    (fun i hi => integrable_unfoldedModeDensity hI himage hJ hinj hg hD (hqI i hi) hn (hjn i hi))
    (fun i hi => integrable_unfoldedModeDensity hI himage hJ hinj hg hD (hwI i hi) hn (hjn i hi))
    (T := fun i a => ((index i:ℝ)+((index i:ℝ)/n)*J a)/n)
  · intro i _hi
    fun_prop
  · intro i his
    exact unfoldedModeDensity_pushforward (hq i his) (hq₀ i his)
      ((hqs i his).trans inter_subset_left) ((hqs i his).trans inter_subset_right)
      hj hj₀ hJe hI himage hJ hinj hg hD hn (hjn i his)
  · intro i his
    exact unfoldedModeDensity_pushforward (hw i his) (hw₀ i his)
      ((hws i his).trans inter_subset_left) ((hws i his).trans inter_subset_right)
      hj hj₀ hJe hI himage hJ hinj hg hD hn (hjn i his)

lemma leading_unfolded_residue_eq_sampled
    (I : Set ℝ) (J : ℝ → ℝ) (F : ℝ × ℝ → ℝ)
    {n : ℕ} (hn : 0 < n) (P : ℕ) (h : ℤ) (S : Finset ℤ)
    (hS : ∀ k ∉ S, ∀ a, F (a,((h+k*(P:ℤ):ℤ):ℝ)/n) = 0) (t : ℝ) :
    (∑ k ∈ S, unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (fun a => (n:ℝ)⁻¹*F (a,((h+k*(P:ℤ):ℤ):ℝ)/n)) n ((h+k*(P:ℤ):ℤ):ℝ) t) =
      sampledResidueKernel (passageBranchKernel I J F) P h n t := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp_rw [unfoldedModeDensity_stationary I J F hn']
  unfold sampledResidueKernel
  have he (k : ℤ) : (n:ℝ)*t-((h+k*(P:ℤ):ℤ):ℝ) = (n:ℝ)*t-h-k*P := by push_cast; ring
  simp_rw [he,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  symm
  apply tsum_eq_sum
  intro k hk
  rw [passageBranchKernel_formula]
  have hz (a : ℝ) : F (a,((h:ℝ)+k*P)/n) = 0 := by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using hS k hk a
  simp [branchKernel,hz]

lemma integral_abs_triangle {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g h : X → ℝ} (hfg : Integrable (fun x => |f x-g x|) μ)
    (hgh : Integrable (fun x => |g x-h x|) μ) :
    (∫ x, |f x-h x| ∂μ) ≤ (∫ x, |f x-g x| ∂μ)+(∫ x, |g x-h x| ∂μ) := by
  calc
    _ ≤ ∫ x, |f x-g x|+|g x-h x| ∂μ := integral_mono_of_nonneg
      (Eventually.of_forall (fun _ => abs_nonneg _)) (hfg.add hgh)
      (Eventually.of_forall (fun x => by
        calc
          |f x-h x| = |(f x-g x)+(g x-h x)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _))
    _ = _ := integral_add hfg hgh

lemma passageBranchKernel_integrable_error {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ a s, |s| < ε → F (a,s) = 0) {P n : ℕ} (hP : 0 < P)
    (hn : 0 < n) (h : ℤ) :
    Integrable (fun t =>
      |sampledResidueKernel (passageBranchKernel I J F) P h n t-
        fineResidueKernel (passageBranchKernel I J F) P h n t|) := by
  have hSm := branchKernel_smooth hJ hIo hinj hd hF hc hs
  obtain ⟨D,A,hD,hA,hx,ha⟩ := branchKernel_bounds (I := I) hJ.continuous hc
  have hsmooth := affineKernel_smooth (L := (1:ℝ)) (β := (0:ℝ))
    (hSm.comp (contDiff_snd.prodMk contDiff_fst)) hε (show
      ∀ s a, |s| < ε → branchKernel I J F (a,s) = 0 from fun s a hh => by
        simp [branchKernel,hz _ _ hh])
  obtain ⟨M,hM⟩ := exists_nat_ge (A*((1:ℝ)*D+|(0:ℝ)|))
  apply integrable_sampledResidueKernel_error h hsmooth.continuous
    (fun s y hh => affineKernel_eq_zero_s (fun s a hh => ha a s hh) hh)
    (M := M) _ hn hP
  intro s y hy
  exact affineKernel_eq_zero_y (by norm_num) hA hD
    (fun s a hh => ha a s hh) (fun s a hh => hx a s hh) (lt_of_le_of_lt hM hy)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma sum_residue_le_tsum {E : ℤ → ℝ} (hE : Summable E) (hE0 : ∀ j, 0 ≤ E j)
    {P : ℕ} (hP : 0 < P) (h : ℤ) (S : Finset ℤ) :
    (∑ k ∈ S, E (h+k*(P:ℤ))) ≤ ∑' j : ℤ, E j := by
  have hinj : Injective (fun k : ℤ => h+k*(P:ℤ)) := by
    intro k l he
    exact mul_right_cancel₀ (show (P:ℤ) ≠ 0 by exact_mod_cast hP.ne')
      (add_left_cancel he)
  rw [← Finset.sum_image (fun k _ l _ he => hinj he)]
  exact Summable.sum_le_tsum _ (fun j _ => hE0 j) hE

/-- Full finite retained residue density estimate, at the actual spectral
pushforwards. The right-hand side consists only of coefficient mass error and
the already proved explicit slow-variable freezing error. -/
lemma unfolded_residue_density_error
    {I : Set ℝ} {J₀ : ℝ → ℝ} {J : UnitAddCircle → ℝ} {o : ℝ}
    {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ a s, |s| < ε → F (a,s) = 0)
    (hj : Measurable J) (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    {n P : ℕ} (hn : 0 < n) (hP : 0 < P) (h : ℤ) (S : Finset ℤ)
    (hSN : ∀ k ∈ S, h+k*(P:ℤ) ≠ 0)
    (hST : ∀ k ∉ S, ∀ a, F (a,((h+k*(P:ℤ):ℤ):ℝ)/n) = 0)
    {q w : ℤ → UnitAddCircle → ℝ} {q₀ : ℤ → ℝ → ℝ}
    (hq : ∀ k ∈ S, Integrable (q (h+k*(P:ℤ))) AddCircle.haarAddCircle)
    (hw : ∀ k ∈ S, Integrable (w (h+k*(P:ℤ))) AddCircle.haarAddCircle)
    (hq₀ : ∀ k ∈ S, ∀ x ∈ Ioc o (o+1), q (h+k*(P:ℤ)) (x : UnitAddCircle) = q₀ (h+k*(P:ℤ)) x)
    (hw₀ : ∀ k ∈ S, ∀ x ∈ Ioc o (o+1), w (h+k*(P:ℤ)) (x : UnitAddCircle) =
      (n:ℝ)⁻¹*F (x,((h+k*(P:ℤ):ℤ):ℝ)/n))
    (hqs : ∀ k ∈ S, support (q₀ (h+k*(P:ℤ))) ⊆ Ioc o (o+1) ∩ I)
    (hws : ∀ k ∈ S, support (fun a => (n:ℝ)⁻¹*F (a,((h+k*(P:ℤ):ℤ):ℝ)/n)) ⊆ Ioc o (o+1) ∩ I)
    {E : ℤ → ℝ} (hE : Summable E) (hE0 : ∀ j, 0 ≤ E j)
    (hEB : ∀ k ∈ S, (∫ a, |q (h+k*(P:ℤ)) a-w (h+k*(P:ℤ)) a|
      ∂AddCircle.haarAddCircle) ≤ E (h+k*(P:ℤ))) :
    (∫ t, |(∑ k ∈ S, unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
        (q₀ (h+k*(P:ℤ))) n ((h+k*(P:ℤ):ℤ):ℝ) t)-
      fineResidueKernel (passageBranchKernel I J₀ F) P h n t|) ≤
    (∑' j : ℤ, E j) +
      ∫ t, |sampledResidueKernel (passageBranchKernel I J₀ F) P h n t-
        fineResidueKernel (passageBranchKernel I J₀ F) P h n t| := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hJs (x : ℝ) (hx : x ∈ I) : HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    ((hJ.differentiable (by simp)) x).hasDerivAt.hasDerivWithinAt
  have hg (x : ℝ) (hx : x ∈ I) : invFunOn J₀ I (J₀ x) = x := hinj.leftInvOn_invFunOn hx
  have him : MeasurableSet (J₀ '' I) := (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
  let index : ℤ → ℤ := fun k => h+k*(P:ℤ)
  let w₀ : ℤ → ℝ → ℝ := fun j a => (n:ℝ)⁻¹*F (a,(j:ℝ)/n)
  have hLead (t : ℝ) := leading_unfolded_residue_eq_sampled I J₀ F hn P h S hST t
  have he : (∫ t, |(∑ k ∈ S, unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
        (q₀ (index k)) n (index k) t)-
      sampledResidueKernel (passageBranchKernel I J₀ F) P h n t|) ≤
      ∑ k ∈ S, ∫ a, |q (index k) a-w (index k) a| ∂AddCircle.haarAddCircle := by
    simp_rw [← hLead]
    exact finite_unfolded_index_error hn' S index hSN hq hw hq₀ hw₀ hqs hws
      hj hJ.continuous.measurable hJe hIo.measurableSet him hJs hinj hg hd
  have hqI (k : ℤ) (hk : k ∈ S) : Integrable (q₀ (index k)) := by
    rw [← circleDensityLift_eq (hq₀ k hk) ((hqs k hk).trans inter_subset_left)]
    exact integrable_circleDensityLift (hq k hk) o
  have hwI (k : ℤ) (hk : k ∈ S) : Integrable (w₀ (index k)) := by
    dsimp only [w₀, index]
    rw [← circleDensityLift_eq (hw₀ k hk) ((hws k hk).trans inter_subset_left)]
    exact integrable_circleDensityLift (hw k hk) o
  have hfg : Integrable (fun t => |(∑ k ∈ S,
      unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) (q₀ (index k)) n (index k) t)-
      sampledResidueKernel (passageBranchKernel I J₀ F) P h n t|) := by
    simp_rw [← hLead]
    apply Integrable.abs
    apply Integrable.sub
    · apply integrable_finsetSum
      intro k hk
      exact integrable_unfoldedModeDensity hIo.measurableSet him hJs hinj hg hd (hqI k hk) hn'
        (by exact_mod_cast hSN k hk)
    · apply integrable_finsetSum
      intro k hk
      exact integrable_unfoldedModeDensity hIo.measurableSet him hJs hinj hg hd (hwI k hk) hn'
        (by exact_mod_cast hSN k hk)
  have hsamp := passageBranchKernel_integrable_error hJ hIo hinj hd hF hc hs hε hz hP hn h
  apply (integral_abs_triangle hfg hsamp).trans
  apply add_le_add _ le_rfl
  apply he.trans
  calc
    _ ≤ ∑ k ∈ S, E (index k) := Finset.sum_le_sum hEB
    _ ≤ _ := sum_residue_le_tsum hE hE0 hP h S

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_family_of_branch {Ω : Type*} {C I : Set ℝ}
    {J : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : ∀ a, support (A a) ⊆ I) :
    (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily I J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
  have he (C : Set ℝ) :
      (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
    funext p
    simp only [stationaryWeight,branchDensity,branchFamily]
    split_ifs with h <;> simp [h]
  rw [he]
  apply branchFamily_congr_branch hIC hi
  intro p hp
  refine ⟨hs p.2 ?_,mem_univ _⟩
  intro hz
  apply hp
  simp [hz]

lemma stationaryWeight_signed_compact_continuous {J : ℝ → ℝ}
    {A : UnitAddCircle → ℝ → ℂ} {l u R : ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hA : Continuous A.uncurry) (hs : ∀ a, support (A a) ⊆ Icc l u)
    (hR : 0 < R) (hi : InjOn J (Icc (l-R) (u+R)))
    (hd : ∀ x ∈ Ioo (l-R) (u+R), deriv J x ≠ 0) :
    Continuous (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) ∧
    HasCompactSupport (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) := by
  let F : ℝ × UnitAddCircle → ℝ := fun p => ‖A p.2 p.1‖^2
  have hF : Continuous F := (hA.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2
  have hFs : support F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) := by
    intro p hp
    refine ⟨hs p.2 ?_,mem_univ _⟩
    intro hz
    exact hp (by simp [F,show A p.2 p.1 = 0 from hz])
  have hFt : tsupport F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) :=
    closure_minimal hFs (isClosed_Icc.prod isClosed_univ)
  have hc : HasCompactSupport F :=
    (isCompact_Icc.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport F) hFt
  have hsub : Icc l u ⊆ Ioo (l-R) (u+R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  rw [stationaryWeight_family_of_branch Ioo_subset_Icc_self hi (fun a => (hs a).trans hsub)]
  exact ⟨branchFamily_continuous hJ isOpen_Ioo (hi.mono Ioo_subset_Icc_self) hd hF hc
    (fun p hp => ⟨hsub (hFt hp).1,mem_univ _⟩),branchFamily_compact hJ.continuous hc⟩

/-- Smoothness of the actual old-frequency Jacobian, with a compactly
supported real lift of the old amplitude (including the new good-arc cutoff).
Both positive and negative angular indices are allowed by the injective branch. -/
lemma stationaryWeight_smooth_lift {C I : Set ℝ} {J : ℝ → ℝ} {B : ℝ × ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B) (hc : HasCompactSupport B)
    (hs : tsupport B ⊆ I ×ˢ univ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => stationaryWeight C J (fun x => B (x,p.2)) p.1) ∧
    HasCompactSupport (fun p : ℝ × ℝ => stationaryWeight C J (fun x => B (x,p.2)) p.1) := by
  let F : ℝ × ℝ → ℝ := fun p => ‖B p‖^2
  have hFt : tsupport F ⊆ tsupport B := by
    apply closure_mono
    intro p hp hz
    exact hp (by simp [F,show B p = 0 from hz])
  have hFc : HasCompactSupport F := hc.of_isClosed_subset (isClosed_tsupport F) hFt
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hB.norm_sq (𝕜 := ℂ)
  have hA (a : ℝ) : support (fun x => B (x,a)) ⊆ I := by
    intro x hx
    exact (hs (subset_tsupport B hx)).1
  have he := stationaryWeight_family_of_branch (A := fun a x => B (x,a)) hIC hi hA
  rw [he]
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (branchKernel I J F) ∧
    HasCompactSupport (branchKernel I J F)
  exact ⟨branchKernel_smooth hJ hIo (hi.mono hIC) hd hF hFc (hFt.trans hs),
    branchKernel_compact hJ.continuous hFc⟩

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

/-- A finite retained residue index set exists for every positive passage
integer. Its zero mode is excluded by the cutoff support, not by a limit. -/
lemma exists_retained_residue_indices {χ : ℝ → UnitAddCircle → ℝ}
    (hc : HasCompactSupport χ.uncurry) (hz : ∀ a, χ 0 a = 0)
    {n P : ℕ} (hn : 0 < n) (hP : 0 < P) (h : ℤ) :
    ∃ S : Finset ℤ, (∀ k ∈ S, h+k*(P:ℤ) ≠ 0) ∧
      ∀ k ∉ S, ∀ a, χ (((h+k*(P:ℤ):ℤ):ℝ)/n) a = 0 := by
  classical
  obtain ⟨T,hT⟩ := compact_lattice_support hc hn 0
  have hinj : Injective (fun k : ℤ => h+k*(P:ℤ)) := by
    intro k l he
    exact mul_right_cancel₀ (show (P:ℤ) ≠ 0 by exact_mod_cast hP.ne') (add_left_cancel he)
  have hf := T.finite_toSet.preimage hinj.injOn
  refine ⟨hf.toFinset.filter (fun k => h+k*(P:ℤ) ≠ 0),?_,?_⟩
  · intro k hk
    exact (Finset.mem_filter.mp hk).2
  · intro k hk a
    by_cases hj : h+k*(P:ℤ) = 0
    · simp [hj,hz]
    · have hk' : h+k*(P:ℤ) ∉ T := by
        intro hkT
        exact hk (Finset.mem_filter.mpr ⟨hf.mem_toFinset.mpr hkT,hj⟩)
      simpa using hT (h+k*(P:ℤ)) hk' a

lemma retainedCircleWeight_integrable {ψ : UnitAddCircle → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (n : ℕ) (j : ℤ) :
    Integrable (retainedCircleWeight ψ χ c n j) AddCircle.haarAddCircle := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
    ((hc n j).norm.pow 2)

lemma retainedCircleWeight_error {ψ : UnitAddCircle → ℝ}
    {χ W : ℝ → UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, W s a ≠ 0 → χ s a = 1)
    (hW : Continuous W.uncurry) (hc : ∀ n j, Continuous (c n j))
    (n : ℕ) (j : ℤ) :
    (∫ a, |retainedCircleWeight ψ χ c n j a-ψ a^2*((n:ℝ)⁻¹*W ((j:ℝ)/n) a)|
      ∂AddCircle.haarAddCircle) ≤
    ∫ a, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle := by
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _))
  · exact ((((hc n j).norm.pow 2).sub (continuous_const.mul
      (hW.comp (continuous_const.prodMk continuous_id)))).abs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · filter_upwards [] with a
    exact cutoff_mass_pointwise (sq_nonneg _) (hχ _ a)
      (fun hh => hχW _ a (fun hw => hh (by rw [hw,mul_zero]))) (hψ a)

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

/-- Full L1 unfolded fine-density convergence for actual retained mode weights.
The only asymptotic input is the summed Fourier coefficient mass theorem;
all pushforward identities, integrability, cutoffs and residue freezing are
proved here, for both signs and without any divisibility constraint on n. -/
lemma retained_unfolded_residue_error
    {I : Set ℝ} {J₀ : ℝ → ℝ} {J : UnitAddCircle → ℝ} {o : ℝ}
    {F : ℝ × ℝ → ℝ} {W χ : ℝ → UnitAddCircle → ℝ}
    {ψ : UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ (Ioc o (o+1) ∩ I) ×ˢ univ)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ a s, |s| < ε → F (a,s) = 0)
    (hj : Measurable J) (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hW : Continuous W.uncurry) (hcW : HasCompactSupport W.uncurry)
    (hcc : ∀ n j, Continuous (c n j))
    (hcs : ∀ n, Summable (fun j => ∫ a, ‖c n j a‖^2 ∂AddCircle.haarAddCircle))
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, W s a ≠ 0 → χ s a = 1)
    (hψS : ∀ x ∈ Ioc o (o+1), ψ (x : UnitAddCircle) ≠ 0 → x ∈ I)
    (hFlift : ∀ x ∈ Ioc o (o+1), ∀ s,
      F (x,s) = ψ (x : UnitAddCircle)^2*W s (x : UnitAddCircle))
    {n P : ℕ} (hn : 0 < n) (hP : 0 < P) (h : ℤ) (S : Finset ℤ)
    (hSN : ∀ k ∈ S, h+k*(P:ℤ) ≠ 0)
    (hST : ∀ k ∉ S, ∀ a, χ (((h+k*(P:ℤ):ℤ):ℝ)/n) a = 0) :
    (∫ t, |(∑ k ∈ S,
      unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
        (circleDensityLift o (retainedCircleWeight ψ χ c n (h+k*(P:ℤ))))
        n ((h+k*(P:ℤ):ℤ):ℝ) t)-
      fineResidueKernel (passageBranchKernel I J₀ F) P h n t|) ≤
    (∑' j : ℤ, ∫ a, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) +
      ∫ t, |sampledResidueKernel (passageBranchKernel I J₀ F) P h n t-
        fineResidueKernel (passageBranchKernel I J₀ F) P h n t| := by
  have hsFI : tsupport F ⊆ I ×ˢ univ := fun p hp => ⟨(hsF hp).1.2,mem_univ _⟩
  let q : ℤ → UnitAddCircle → ℝ := retainedCircleWeight ψ χ c n
  let w : ℤ → UnitAddCircle → ℝ := fun j a => ψ a^2*((n:ℝ)⁻¹*W ((j:ℝ)/n) a)
  let E : ℤ → ℝ := fun j => ∫ a, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a|
    ∂AddCircle.haarAddCircle
  have hEi : Summable E := by
    simpa [E] using integrated_array_mass_error_summable hW hcW (hcc n) (hcs n) hn 0
  have hq (j : ℤ) : Integrable (q j) AddCircle.haarAddCircle :=
    retainedCircleWeight_integrable hψc hχc hcc n j
  have hw (j : ℤ) : Integrable (w j) AddCircle.haarAddCircle :=
    ((hψc.pow 2).mul (continuous_const.mul
      (hW.comp (continuous_const.prodMk continuous_id)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hq₀ (j : ℤ) (x : ℝ) (hx : x ∈ Ioc o (o+1)) :
      q j (x : UnitAddCircle) = circleDensityLift o (q j) x := by
    simp only [circleDensityLift,indicator_of_mem hx]
  have hw₀ (j : ℤ) (x : ℝ) (hx : x ∈ Ioc o (o+1)) :
      w j (x : UnitAddCircle) = (n:ℝ)⁻¹*F (x,(j:ℝ)/n) := by
    rw [hFlift x hx]; dsimp [w]; ring
  have hqs (j : ℤ) : support (circleDensityLift o (q j)) ⊆ Ioc o (o+1) ∩ I := by
    intro x hx
    have hxI : x ∈ Ioc o (o+1) := by
      by_contra hh
      exact hx (by simp [circleDensityLift,hh])
    refine ⟨hxI,hψS x hxI ?_⟩
    intro hz
    exact hx (by simp [circleDensityLift,hxI,q,retainedCircleWeight,hz])
  have hws (j : ℤ) : support (fun a => (n:ℝ)⁻¹*F (a,(j:ℝ)/n)) ⊆ Ioc o (o+1) ∩ I := by
    intro a ha
    have hf : F (a,(j:ℝ)/n) ≠ 0 := fun hh => ha (by simp [hh])
    exact (hsF (subset_tsupport F hf)).1
  have hSTF (k : ℤ) (hk : k ∉ S) (a : ℝ) :
      F (a,((h+k*(P:ℤ):ℤ):ℝ)/n) = 0 := by
    by_contra hh
    have ha := (hsF (subset_tsupport F hh)).1.1
    rw [hFlift a ha] at hh
    have hw' : W (((h+k*(P:ℤ):ℤ):ℝ)/n) (a : UnitAddCircle) ≠ 0 :=
      fun hw' => hh (by rw [hw',mul_zero])
    have h1 := hχW _ _ hw'
    rw [hST k hk] at h1
    norm_num at h1
  exact unfolded_residue_density_error (o := o) (n := n) (q := q) (w := w)
    (q₀ := fun j => circleDensityLift o (q j)) (E := E)
    hJ hIo hinj hd hF hcF hsFI hε hz hj hJe hn hP h S
    (hSN) hSTF (fun k _ => hq _) (fun k _ => hw _) (fun k _ => hq₀ _)
    (fun k _ => hw₀ _) (fun k _ => hqs _) (fun k _ => hws _)
    hEi (fun j => integral_nonneg (fun a => abs_nonneg _))
    (fun k _ => retainedCircleWeight_error hψ hχ hχW hW hcc n _)

lemma retained_unfolded_residue_tendsto
    {I : Set ℝ} {J₀ : ℝ → ℝ} {J : UnitAddCircle → ℝ} {o : ℝ}
    {F : ℝ × ℝ → ℝ} {W χ : ℝ → UnitAddCircle → ℝ}
    {ψ : UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ (Ioc o (o+1) ∩ I) ×ˢ univ)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ a s, |s| < ε → F (a,s) = 0)
    (hj : Measurable J) (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hW : Continuous W.uncurry) (hcW : HasCompactSupport W.uncurry)
    (hcc : ∀ n j, Continuous (c n j))
    (hcs : ∀ n, Summable (fun j => ∫ a, ‖c n j a‖^2 ∂AddCircle.haarAddCircle))
    (hmass : Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a,
      |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) atTop (𝓝 0))
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, W s a ≠ 0 → χ s a = 1)
    (hψS : ∀ x ∈ Ioc o (o+1), ψ (x : UnitAddCircle) ≠ 0 → x ∈ I)
    (hFlift : ∀ x ∈ Ioc o (o+1), ∀ s,
      F (x,s) = ψ (x : UnitAddCircle)^2*W s (x : UnitAddCircle))
    {P : ℕ} (hP : 0 < P) (h : ℤ) (S : ℕ → Finset ℤ)
    (hSN : ∀ n, 0 < n → ∀ k ∈ S n, h+k*(P:ℤ) ≠ 0)
    (hST : ∀ n, 0 < n → ∀ k ∉ S n, ∀ a,
      χ (((h+k*(P:ℤ):ℤ):ℝ)/n) a = 0) :
    Tendsto (fun n : ℕ => ∫ t, |(∑ k ∈ S n,
      unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
        (circleDensityLift o (retainedCircleWeight ψ χ c n (h+k*(P:ℤ))))
        n ((h+k*(P:ℤ):ℤ):ℝ) t)-
      fineResidueKernel (passageBranchKernel I J₀ F) P h n t|) atTop (𝓝 0) := by
  have hsFI : tsupport F ⊆ I ×ˢ univ := fun p hp => ⟨(hsF hp).1.2,mem_univ _⟩
  have hfreeze := passageBranchKernel_fine_density hJ hIo hinj hd hF hcF hsFI hε hz hP h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_add] using hmass.add hfreeze)
  · exact Eventually.of_forall (fun n => integral_nonneg (fun t => abs_nonneg _))
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact retained_unfolded_residue_error hJ hIo hinj hd hF hcF hsF hε hz hj hJe hW hcW
    hcc hcs hψc hχc hψ hχ hχW hψS hFlift hn hP h (S n) (hSN n hn) (hST n hn)

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma scaled_speed_good_branch {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x) :
    InjOn (fun x => (m:ℝ)*V x) (Icc (l-R) (u+R)) ∧
      ∀ x ∈ Ioo (l-R) (u+R), deriv (fun x => (m:ℝ)*V x) x ≠ 0 := by
  have hsub : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : InjOn V (Icc (l-R) (u+R)) :=
    (strictMonoOn_of_deriv_pos (convex_Icc _ _) hV.continuous.continuousOn
      (fun x hx => hd x (hsub (interior_subset hx)))).injOn
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  refine ⟨?_,?_⟩
  · intro x hx y hy he
    exact hi hx hy (mul_left_cancel₀ hm' he)
  · intro x hx
    rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_ne_zero hm' (hd x (hsub (Ioo_subset_Icc_self hx))).ne'

/-- The fine temporal density assertion of the Passage Lemma for one actual
old packet. There are no asymptotic or numerical stationary-phase estimates
among the hypotheses: the exact signed Fourier mass theorem supplies them.
The smooth real lift F is the cutoff old-frequency Jacobian, with its precise
identity stated below. -/
lemma exact_retained_unfolded_residue_tendsto
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0))
    {I : Set ℝ} {J₀ : ℝ → ℝ} {J : UnitAddCircle → ℝ} {o' : ℝ}
    {F : ℝ × ℝ → ℝ} {χ : ℝ → UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ (Ioc o' (o'+1) ∩ I) ×ˢ univ)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ a s, |s| < ε → F (a,s) = 0)
    (hj : Measurable J) (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    (hψS : ∀ x ∈ Ioc o' (o'+1), ψ (x : UnitAddCircle) ≠ 0 → x ∈ I)
    (hFlift : ∀ x ∈ Ioc o' (o'+1), ∀ s,
      F (x,s) = ψ (x : UnitAddCircle)^2*
        stationaryWeight (Icc (l-R) (u+R)) (fun u => (m:ℝ)*V u) (A₀ (x : UnitAddCircle)) s)
    {Q : ℕ} (hQ : 0 < Q) (h : ℤ) (S : ℕ → Finset ℤ)
    (hSN : ∀ n, 0 < n → ∀ k ∈ S n, h+k*(Q:ℤ) ≠ 0)
    (hST : ∀ n, 0 < n → ∀ k ∉ S n, ∀ a,
      χ (((h+k*(Q:ℤ):ℤ):ℝ)/n) a = 0) :
    Tendsto (fun n : ℕ => ∫ t, |(∑ k ∈ S n,
      unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
        (circleDensityLift o' (retainedCircleWeight ψ χ
          (fun n j => exactPassageCoeff m (H n) A j) n (h+k*(Q:ℤ))))
        n ((h+k*(Q:ℤ):ℤ):ℝ) t)-
      fineResidueKernel (passageBranchKernel I J₀ F) Q h n t|) atTop (𝓝 0) := by
  have hbranch := scaled_speed_good_branch hm hR hV hdV
  have hW := stationaryWeight_signed_compact_continuous (contDiff_const.mul hV) hAc
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hR hbranch.1 hbranch.2
  have hmass := exactPassageCoeff_summed hm hH hA hA₀ hAc hAd hsupp hlo huo hlu hR
    hPr hV hPV hdV hHc hAcont hδt
  exact retained_unfolded_residue_tendsto
    (W := fun s a => stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s)
    (c := fun n j => exactPassageCoeff m (H n) A j)
    hJ hIo hinj hd hF hcF hsF hε hz hj hJe hW.1 hW.2
    (fun n j => continuous_exactPassageCoeff (hHc n) hAcont j)
    (fun n => exactPassageCoeff_summable (hHc n) hAcont) hmass hψc hχc hψ hχ hχW hψS hFlift
    hQ h S hSN hST

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_mul (C : Set ℝ) (J : ℝ → ℝ) (A : ℝ → ℂ) (c : ℂ) (s : ℝ) :
    stationaryWeight C J (fun x => c*A x) s = ‖c‖^2*stationaryWeight C J A s := by
  classical
  unfold stationaryWeight branchDensity
  simp only [Set.indicator_apply]
  split_ifs <;> simp [mul_pow,mul_div_assoc]

lemma stationaryCutoffLift_eq {C : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ} :
    stationaryCutoffLift C J A ψ = fun p : ℝ × ℝ =>
      stationaryWeight C J (fun x => (ψ p.1 : ℂ)*A (x,p.1)) p.2 := by
  funext p
  rw [stationaryWeight_mul]
  simp [stationaryCutoffLift,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma cutoff_amplitude_regular {K : Set ℝ} {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K) (hK : IsCompact K)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (ψ p.2 : ℂ)*A p) ∧
      HasCompactSupport (fun p : ℝ × ℝ => (ψ p.2 : ℂ)*A p) ∧
      tsupport (fun p : ℝ × ℝ => (ψ p.2 : ℂ)*A p) ⊆ K ×ˢ tsupport ψ := by
  let B : ℝ × ℝ → ℂ := fun p => (ψ p.2 : ℂ)*A p
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B :=
    (Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_snd)).mul hA
  have hsB : tsupport B ⊆ K ×ˢ tsupport ψ := by
    apply closure_minimal _ (hK.isClosed.prod (isClosed_tsupport ψ))
    intro p hp
    have ha : A p ≠ 0 := fun hz => hp (by simp [B,hz])
    have hψn : ψ p.2 ≠ 0 := fun hz => hp (by simp [B,hz])
    exact ⟨hKA p ha,subset_tsupport ψ hψn⟩
  have hcB : HasCompactSupport B :=
    (hK.prod hcψ).of_isClosed_subset (isClosed_tsupport B) hsB
  exact ⟨hB,hcB,hsB⟩

lemma stationaryCutoffLift_regular {C I K : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hIC : I ⊆ C) (hi : InjOn J C)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K) (hK : IsCompact K) (hKI : K ⊆ I)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (stationaryCutoffLift C J A ψ) ∧
      HasCompactSupport (stationaryCutoffLift C J A ψ) := by
  let B : ℝ × ℝ → ℂ := fun p => (ψ p.2 : ℂ)*A p
  obtain ⟨hB,hcB,hsB⟩ := cutoff_amplitude_regular hA hKA hK hψ hcψ
  have hsBI : tsupport B ⊆ I ×ˢ univ := fun p hp => ⟨hKI (hsB hp).1,mem_univ _⟩
  have h := stationaryWeight_smooth_lift (C := C) (I := I) (J := J) (B := B)
    hIC hi hJ hIo hd hB hcB hsBI
  let G : ℝ × ℝ → ℝ := fun p => stationaryWeight C J (fun x => B (x,p.2)) p.1
  have hswap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
    contDiff_snd.prodMk contDiff_fst
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G ∘ Prod.swap) := h.1.comp hswap
  have hc : HasCompactSupport (G ∘ Prod.swap) :=
    h.2.comp_homeomorph (Homeomorph.prodComm ℝ ℝ)
  have he : stationaryCutoffLift C J A ψ = G ∘ Prod.swap := stationaryCutoffLift_eq
  rw [he]
  exact ⟨hs,hc⟩

lemma stationaryWeight_support_subset {C K : Set ℝ} {J : ℝ → ℝ} {A : ℝ → ℂ}
    (hA : support A ⊆ K) : support (stationaryWeight C J A) ⊆ J '' K := by
  classical
  intro s hs
  have hsC : s ∈ J '' C := by
    by_contra hn
    exact hs (by simp [stationaryWeight,branchDensity,hn])
  have hp := invFunOn_pos hsC
  refine ⟨invFunOn J C s,hA ?_,hp.2⟩
  intro hz
  exact hs (by simp [stationaryWeight,branchDensity,hsC,show A (invFunOn J C s) = 0 from hz])

lemma stationaryCutoffLift_support {C K : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hJ : Continuous J) (hK : IsCompact K) (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K) :
    tsupport (stationaryCutoffLift C J A ψ) ⊆ tsupport ψ ×ˢ (J '' K) := by
  apply closure_minimal _ ((isClosed_tsupport ψ).prod (hK.image hJ).isClosed)
  intro p hp
  have hψn : ψ p.1 ≠ 0 := fun hz => hp (by simp [stationaryCutoffLift,hz])
  have hWn : stationaryWeight C J (fun x => A (x,p.1)) p.2 ≠ 0 :=
    fun hz => hp (by simp [stationaryCutoffLift,hz])
  exact ⟨subset_tsupport ψ hψn,
    stationaryWeight_support_subset (fun x hx => hKA (x,p.1) hx) hWn⟩

lemma stationaryCutoffLift_zero_near_zero {C K : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hJ : Continuous J) (hK : IsCompact K) (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K)
    (h0 : 0 ∉ J '' K) :
    ∃ ε > 0, ∀ a s, |s| < ε → stationaryCutoffLift C J A ψ (a,s) = 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ((hK.image hJ).isClosed.isOpen_compl.mem_nhds h0)
  refine ⟨ε,hε,?_⟩
  intro a s hs
  by_contra hh
  have hh' := stationaryCutoffLift_support hJ hK hKA (subset_tsupport _ hh)
  exact hball (by simpa [Metric.mem_ball,Real.dist_eq] using hs) hh'.2

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma exists_retained_residue_sequence {χ : ℝ → UnitAddCircle → ℝ}
    (hc : HasCompactSupport χ.uncurry) (hz : ∀ a, χ 0 a = 0)
    {P : ℕ} (hP : 0 < P) (h : ℤ) :
    ∃ S : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ k ∈ S n, h+k*(P:ℤ) ≠ 0) ∧
      ∀ n, 0 < n → ∀ k ∉ S n, ∀ a, χ (((h+k*(P:ℤ):ℤ):ℝ)/n) a = 0 := by
  classical
  have hs (n : ℕ) : ∃ S : Finset ℤ,
      (0 < n → ∀ k ∈ S, h+k*(P:ℤ) ≠ 0) ∧
      (0 < n → ∀ k ∉ S, ∀ a, χ (((h+k*(P:ℤ):ℤ):ℝ)/n) a = 0) := by
    by_cases hn : 0 < n
    · obtain ⟨S,hS,hT⟩ := exists_retained_residue_indices hc hz hn hP h
      exact ⟨S,fun _ => hS,fun _ => hT⟩
    · exact ⟨∅,fun hh => (hn hh).elim,fun hh => (hn hh).elim⟩
  choose S hN hT using hs
  exact ⟨S,hN,hT⟩

/-- The cutoff old-frequency Jacobian used in the Passage Lemma has all
required regularity, including the frequency gap. These conclusions are
derived from the actual smooth amplitude and compact cutoffs. -/
lemma exact_cutoff_weight_regular
    {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ} {A₀ : UnitAddCircle → ℝ → ℂ} {ψ₀ : ℝ → ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Icc l u)
    (hψ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hcψ₀ : HasCompactSupport ψ₀)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u) :
    let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1) ψ₀
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧ HasCompactSupport F ∧
      ∃ ε > 0, ∀ a s, |s| < ε → F (a,s) = 0 := by
  dsimp only
  have hb := scaled_speed_good_branch hm hR hV hdV
  have hKI : Icc l u ⊆ Ioo (l-R) (u+R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hKA : ∀ p : ℝ × ℝ, A₀ (p.2 : UnitAddCircle) p.1 ≠ 0 → p.1 ∈ Icc l u :=
    fun p hp => hsupp _ hp
  have h := stationaryCutoffLift_regular Ioo_subset_Icc_self hb.1 (contDiff_const.mul hV)
    isOpen_Ioo hb.2 hAr hKA isCompact_Icc hKI hψ₀ hcψ₀
  exact ⟨h.1,h.2,stationaryCutoffLift_zero_near_zero
    (continuous_const.mul hV.continuous) isCompact_Icc hKA h0⟩

/-- Source Passage Lemma, exact unfolded spectral conclusion for any residue
of one signed packet. The Fourier coefficients, cutoff weight and fine kernel
are all the displayed source objects. Smooth compact lift, finite retention
and frequency-gap obligations are produced here, not postulated as analytic
estimates. Geometry and physical Fourier transport are separate proved lemmas. -/
lemma exact_passage_unfolded_spectral_limit
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0))
    {I : Set ℝ} {J₀ : ℝ → ℝ} {J : UnitAddCircle → ℝ} {o' : ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hj : Measurable J) (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hψ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hcψ₀ : HasCompactSupport ψ₀)
    (hsψ₀ : tsupport ψ₀ ⊆ Ioc o' (o'+1) ∩ I)
    (heψ : ∀ x ∈ Ioc o' (o'+1), ψ₀ x = ψ (x : UnitAddCircle))
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry)
    (hzχ : ∀ a, χ 0 a = 0)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {Q : ℕ} (hQ : 0 < Q) (h : ℤ) :
    let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1) ψ₀
    ∃ S : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ k ∈ S n, h+k*(Q:ℤ) ≠ 0) ∧
      (∀ n, 0 < n → ∀ k ∉ S n, ∀ a, χ (((h+k*(Q:ℤ):ℤ):ℝ)/n) a = 0) ∧
      Tendsto (fun n : ℕ => ∫ t, |(∑ k ∈ S n,
        unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
          (circleDensityLift o' (retainedCircleWeight ψ χ
            (fun n j => exactPassageCoeff m (H n) A j) n (h+k*(Q:ℤ))))
          n ((h+k*(Q:ℤ):ℤ):ℝ) t)-
        fineResidueKernel (passageBranchKernel I J₀ F) Q h n t|) atTop (𝓝 0) := by
  let B : ℝ × ℝ → ℂ := fun p => A₀ (p.2 : UnitAddCircle) p.1
  let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) B ψ₀
  change ∃ S, _
  obtain ⟨hF,hcF,ε,hε,hz⟩ := exact_cutoff_weight_regular hm hR hV hdV hAr
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hψ₀ hcψ₀ h0
  have hKA : ∀ p : ℝ × ℝ, B p ≠ 0 → p.1 ∈ Icc l u :=
    fun p hp => Ioc_subset_Icc_self (hsupp _ hp)
  have hsF : tsupport F ⊆ (Ioc o' (o'+1) ∩ I) ×ˢ univ := by
    intro p hp
    exact ⟨hsψ₀ (stationaryCutoffLift_support (continuous_const.mul hV.continuous)
      isCompact_Icc hKA hp).1,mem_univ _⟩
  have hψS : ∀ x ∈ Ioc o' (o'+1), ψ (x : UnitAddCircle) ≠ 0 → x ∈ I := by
    intro x hx hn
    exact (hsψ₀ (subset_tsupport ψ₀ (by simpa only [mem_support, heψ x hx] using hn))).2
  have hFlift : ∀ x ∈ Ioc o' (o'+1), ∀ s,
      F (x,s) = ψ (x : UnitAddCircle)^2*
        stationaryWeight (Icc (l-R) (u+R)) (fun u => (m:ℝ)*V u) (A₀ (x : UnitAddCircle)) s := by
    intro x hx s
    simp only [F,stationaryCutoffLift,heψ x hx,B]
  obtain ⟨S,hSN,hST⟩ := exists_retained_residue_sequence hcχ hzχ hQ h
  refine ⟨S,hSN,hST,?_⟩
  exact exact_retained_unfolded_residue_tendsto hm hH hA hA₀ hAc hAd hsupp hlo huo hlu hR
    hPr hV hPV hdV hHc hAcont hδt hJ hIo hinj hd hF hcF hsF hε hz hj hJe
    hψc hχc hψ hχ hχW hψS hFlift hQ h S hSN hST

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology ENNReal
namespace ThreeTorus

lemma measurable_periodizedReal {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (periodizedReal q) := by
  exact Measurable.tsum (fun k => hq.comp (measurable_id.add_const (k:ℝ)))

lemma measurable_foldCircleDensity {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (foldCircleDensity q) := by
  exact ((measurable_periodizedReal hq).comp measurable_subtype_coe).comp
    (AddCircle.measurableEquivIoc 1 0).measurable

lemma foldCircleDensity_coe {q : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioc 0 1) :
    foldCircleDensity q (x : UnitAddCircle) = periodizedReal q x := by
  exact AddCircle.liftIoc_coe_apply (by simpa using hx)

lemma integral_real_eq_lattice (q : ℝ → ℝ) (hq : Integrable q) :
    (∫ x, q x) = ∑' k : ℤ, ∫ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).integral_eq_tsum'' q hq
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma lintegral_real_eq_lattice (q : ℝ → ℝ≥0∞) :
    (∫⁻ x, q x) = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).lintegral_eq_tsum'' q
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma integrableOn_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    IntegrableOn (periodizedReal q) (Ioc 0 1) := by
  refine ⟨(measurable_periodizedReal hm).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ x in Ioc (0:ℝ) 1, ‖periodizedReal q x‖ₑ) ≤
        ∫⁻ x in Ioc (0:ℝ) 1, ∑' k : ℤ, ‖q (x+k)‖ₑ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, ‖q (x+k)‖ₑ :=
      lintegral_tsum (fun k => (hm.comp (measurable_id.add_const (k:ℝ))).enorm.aemeasurable)
    _ = ∫⁻ x, ‖q x‖ₑ := (lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)).symm
    _ < ∞ := hq.hasFiniteIntegral

lemma integral_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ x in Ioc (0:ℝ) 1, periodizedReal q x) = ∫ x, q x := by
  change (∫ x in Ioc (0:ℝ) 1, ∑' k : ℤ, q (x+k)) = ∫ x, q x
  rw [integral_tsum]
  · exact (integral_real_eq_lattice q hq).symm
  · exact fun k => (hm.comp (measurable_id.add_const (k:ℝ))).aestronglyMeasurable
  · rw [← lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)]
    exact hq.hasFiniteIntegral.ne

lemma integrable_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    Integrable (foldCircleDensity q) AddCircle.haarAddCircle := by
  have hp : MeasurePreserving (fun x : ℝ => (x:UnitAddCircle))
      (volume.restrict (Ioc (0:ℝ) 1)) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 0
  apply (hp.integrable_comp (measurable_foldCircleDensity hm).aestronglyMeasurable).1
  exact (integrableOn_periodizedReal hm hq).congr
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (foldCircleDensity_coe hx).symm))

lemma integral_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ a, foldCircleDensity q a ∂AddCircle.haarAddCircle) = ∫ x, q x := by
  have he := AddCircle.integral_preimage 1 0 (foldCircleDensity q)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,
    one_smul] at he
  rw [← he]
  exact (setIntegral_congr_fun measurableSet_Ioc (fun x hx => foldCircleDensity_coe hx)).trans
    (integral_periodizedReal hm hq)

lemma quotient_add_int (x : ℝ) (k : ℤ) : ((x+k : ℝ):UnitAddCircle) = (x:UnitAddCircle) := by
  have h : ((k:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨k,by simp⟩
  rw [AddCircle.coe_add,h,add_zero]

lemma foldCircleDensity_indicator (q : ℝ → ℝ) (s : Set UnitAddCircle) :
    foldCircleDensity (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) =
      s.indicator (foldCircleDensity q) := by
  classical
  funext a
  let x : ℝ := (AddCircle.equivIoc 1 0 a).1
  have hx : x ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 a).2
  have ha : (x:UnitAddCircle) = a := (AddCircle.equivIoc 1 0).symm_apply_apply a
  rw [← ha]
  by_cases hs : (x:UnitAddCircle) ∈ s
  · simp only [indicator_of_mem hs,foldCircleDensity_coe hx,periodizedReal]
    apply tsum_congr
    intro k
    exact indicator_of_mem (by simpa only [mem_preimage,quotient_add_int] using hs) q
  · simp only [indicator_of_notMem hs,foldCircleDensity_coe hx,periodizedReal]
    have hz (k : ℤ) : (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) (x+k) = 0 :=
      indicator_of_notMem (by simpa only [mem_preimage,quotient_add_int] using hs) q
    simp only [hz,tsum_zero]

/-- Folding is exactly pushforward under the quotient, not a replacement kernel. -/
lemma foldCircleDensity_pushforward {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    ((volume : Measure ℝ).withDensityᵥ q).map (fun x : ℝ => (x:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ (foldCircleDensity q) := by
  ext s hs
  rw [VectorMeasure.map_apply _ AddCircle.measurable_mk' hs,
    withDensityᵥ_apply hq (AddCircle.measurable_mk' hs),
    withDensityᵥ_apply (integrable_foldCircleDensity hm hq) hs,
    ← integral_indicator (AddCircle.measurable_mk' hs),← integral_indicator hs]
  rw [← foldCircleDensity_indicator]
  exact (integral_foldCircleDensity (hm.indicator (AddCircle.measurable_mk' hs))
    (hq.indicator (AddCircle.measurable_mk' hs))).symm

lemma foldCircleDensity_l1_difference {q r : ℝ → ℝ}
    (hqm : Measurable q) (hqi : Integrable q) (hrm : Measurable r) (hri : Integrable r) :
    (∫ a, |foldCircleDensity q a-foldCircleDensity r a| ∂AddCircle.haarAddCircle) ≤
      ∫ x, |q x-r x| := by
  exact l1_pushforward_difference hqi hri (integrable_foldCircleDensity hqm hqi)
    (integrable_foldCircleDensity hrm hri) AddCircle.measurable_mk'
    (foldCircleDensity_pushforward hqm hqi) (foldCircleDensity_pushforward hrm hri)

lemma foldCircleDensity_l1_tendsto {ι : Type*} {l : Filter ι} {q r : ι → ℝ → ℝ}
    (hqm : ∀ᶠ n in l, Measurable (q n)) (hqi : ∀ᶠ n in l, Integrable (q n))
    (hrm : ∀ᶠ n in l, Measurable (r n)) (hri : ∀ᶠ n in l, Integrable (r n))
    (ht : Filter.Tendsto (fun n => ∫ x, |q n x-r n x|) l (𝓝 0)) :
    Filter.Tendsto (fun n => ∫ a, |foldCircleDensity (q n) a-foldCircleDensity (r n) a|
      ∂AddCircle.haarAddCircle) l (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))) ?_ ht
  filter_upwards [hqm,hqi,hrm,hri] with n hqm hqi hrm hri
  exact foldCircleDensity_l1_difference hqm hqi hrm hri

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma measurable_branchDensity_smooth {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) :
    Measurable (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let S := J '' I
  let g := S.piecewise (invFunOn J I) (fun _ => 0)
  have hS : IsOpen S := isOpen_image_of_deriv_ne_zero hJ hIo hd
  have hgi : ContinuousOn (invFunOn J I) S := by
    rintro y ⟨x,hx,rfl⟩
    exact (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hx
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hgi.measurable_piecewise continuous_const.continuousOn hS.measurableSet
  have he : branchDensity I J (invFunOn J I) (deriv J) q =
      S.indicator (fun y => q (g y)/|deriv J (g y)|) := by
    funext y
    by_cases hy : y ∈ S
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp [g,hy]
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp only [indicator_of_notMem hy]
  rw [he]
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  exact ((hq.comp hg).div ((hD.continuous.measurable.comp hg).abs)).indicator hS.measurableSet

lemma measurable_circleDensityLift {q : UnitAddCircle → ℝ} (hq : Measurable q) (o : ℝ) :
    Measurable (circleDensityLift o q) :=
  (hq.comp AddCircle.measurable_mk').indicator measurableSet_Ioc

lemma measurable_unfoldedModeDensity {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) (n j : ℝ) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hm := measurable_branchDensity_smooth hJ hIo hinj hd (hq.const_mul n)
  unfold unfoldedModeDensity scaledBranchKernel
  exact (hm.comp ((measurable_const.mul measurable_id).sub_const j |>.div_const (j/n))).const_mul |j/n|⁻¹

lemma passageBranchKernel_regular {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ a s, |s| < ε → F (a,s) = 0) :
    Continuous (passageBranchKernel I J F).uncurry ∧
      ∃ A > 0, ∃ M : ℕ,
        (∀ s y, A < |s| → passageBranchKernel I J F s y = 0) ∧
        ∀ s y, (M:ℝ) < |y| → passageBranchKernel I J F s y = 0 := by
  have hSm := branchKernel_smooth hJ hIo hinj hd hF hc hs
  obtain ⟨D,A,hD,hA,hx,ha⟩ := branchKernel_bounds (I := I) hJ.continuous hc
  have hsmooth := affineKernel_smooth (L := (1:ℝ)) (β := (0:ℝ))
    (hSm.comp (contDiff_snd.prodMk contDiff_fst)) hε (show
      ∀ s a, |s| < ε → branchKernel I J F (a,s) = 0 from fun s a hh => by
        simp [branchKernel,hz _ _ hh])
  obtain ⟨M,hM⟩ := exists_nat_ge (A*((1:ℝ)*D+|(0:ℝ)|))
  refine ⟨hsmooth.continuous,max A 1,lt_max_of_lt_right zero_lt_one,M,?_,?_⟩
  · intro s y hh
    exact affineKernel_eq_zero_s (fun s a hh => ha a s hh) (lt_of_le_of_lt (le_max_left _ _) hh)
  · intro s y hy
    exact affineKernel_eq_zero_y (by norm_num) hA hD
      (fun s a hh => ha a s hh) (fun s a hh => hx a s hh) (lt_of_le_of_lt hM hy)

lemma fineResidueKernel_regular {K : ℝ → ℝ → ℝ} {A : ℝ} {M n P : ℕ}
    (hK : Continuous K.uncurry) (_hA : 0 < A)
    (hs : ∀ s y, A < |s| → K s y = 0)
    (hy : ∀ s y, (M:ℝ) < |y| → K s y = 0)
    ( _hn : 0 < n) (hP : 0 < P) (h : ℤ) :
    Continuous (fineResidueKernel K P h n) ∧ Integrable (fineResidueKernel K P h n) := by
  have hc := continuous_fineResidueKernel (n := n) h hK hs hy hP
  refine ⟨hc,hc.integrable_of_hasCompactSupport ?_⟩
  apply HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A))
  intro t ht
  apply fineResidueKernel_eq_zero hs
  by_contra hh
  exact ht ⟨(abs_le.mp (le_of_not_gt hh)).1,(abs_le.mp (le_of_not_gt hh)).2⟩

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma retained_unfolded_regular {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (o : ℝ) {n : ℕ} (hn : 0 < n) {j : ℤ} (hj : j ≠ 0) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (circleDensityLift o (retainedCircleWeight ψ χ c n j)) n j) ∧
    Integrable (unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (circleDensityLift o (retainedCircleWeight ψ χ c n j)) n j) := by
  have hq : Continuous (retainedCircleWeight ψ χ c n j) :=
    ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
      ((hc n j).norm.pow 2)
  exact ⟨measurable_unfoldedModeDensity hJ hIo hinj hd
      (measurable_circleDensityLift hq.measurable o) n j,
    integrable_unfoldedModeDensity hIo.measurableSet
      (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
      (fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt) hinj
      (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
      (integrable_circleDensityLift (retainedCircleWeight_integrable hψ hχ hc n j) o)
      (by exact_mod_cast hn) (by exact_mod_cast hj)⟩

/-- Exact contraction of the retained unfolded residue limit to the temporal
circle. In particular the quotient's offsets are not discarded. -/
lemma retained_circle_of_unfolded_limit
    {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    (hsF : tsupport F ⊆ I ×ˢ univ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ a s, |s| < ε → F (a,s) = 0)
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (o : ℝ) {P : ℕ} (hP : 0 < P) (h : ℤ) (S : ℕ → Finset ℤ)
    (hSN : ∀ n, 0 < n → ∀ k ∈ S n, h+k*(P:ℤ) ≠ 0)
    (ht : Tendsto (fun n : ℕ => ∫ t, |(∑ k ∈ S n,
      unfoldedModeDensity I J (invFunOn J I) (deriv J)
        (circleDensityLift o (retainedCircleWeight ψ χ c n (h+k*(P:ℤ))))
        n ((h+k*(P:ℤ):ℤ):ℝ) t)-
      fineResidueKernel (passageBranchKernel I J F) P h n t|) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ a, |foldCircleDensity (fun t => ∑ k ∈ S n,
      unfoldedModeDensity I J (invFunOn J I) (deriv J)
        (circleDensityLift o (retainedCircleWeight ψ χ c n (h+k*(P:ℤ))))
        n ((h+k*(P:ℤ):ℤ):ℝ) t) a-
      foldCircleDensity (fineResidueKernel (passageBranchKernel I J F) P h n) a|
      ∂AddCircle.haarAddCircle) atTop (𝓝 0) := by
  obtain ⟨hK,A,hA,M,hsK,hyK⟩ := passageBranchKernel_regular hJ hIo hinj hd hF hcF hsF hε hz
  have hreg (n : ℕ) (hn : 0 < n) := fineResidueKernel_regular hK hA hsK hyK hn hP h
  apply foldCircleDensity_l1_tendsto (ht := ht)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (S n).measurable_fun_sum (fun k hk =>
      (retained_unfolded_regular hJ hIo hinj hd hψ hχ hc o hn (hSN n hn k hk)).1)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact integrable_finsetSum _ (fun k hk =>
      (retained_unfolded_regular hJ hIo hinj hd hψ hχ hc o hn (hSN n hn k hk)).2)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hreg n hn).1.measurable
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hreg n hn).2

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology
/-- Source Passage Lemma, exact unfolded spectral conclusion for any residue
of one signed packet. The Fourier coefficients, cutoff weight and fine kernel
are all the displayed source objects. Smooth compact lift, finite retention
and frequency-gap obligations are produced here, not postulated as analytic
estimates. Geometry and physical Fourier transport are separate proved lemmas. -/
lemma exact_passage_circle_spectral_limit_oai
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0))
    {I : Set ℝ} {J₀ : ℝ → ℝ} {J : UnitAddCircle → ℝ} {o' : ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀) (hIo : IsOpen I)
    (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hj : Measurable J) (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hψ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hcψ₀ : HasCompactSupport ψ₀)
    (hsψ₀ : tsupport ψ₀ ⊆ Ioc o' (o'+1) ∩ I)
    (heψ : ∀ x ∈ Ioc o' (o'+1), ψ₀ x = ψ (x : UnitAddCircle))
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry)
    (hzχ : ∀ a, χ 0 a = 0)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {Q : ℕ} (hQ : 0 < Q) (h : ℤ) :
    let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1) ψ₀
    ∃ S : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ k ∈ S n, h+k*(Q:ℤ) ≠ 0) ∧
      (∀ n, 0 < n → ∀ k ∉ S n, ∀ a, χ (((h+k*(Q:ℤ):ℤ):ℝ)/n) a = 0) ∧
      Tendsto (fun n : ℕ => ∫ a, |foldCircleDensity (fun t => ∑ k ∈ S n,
        unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
          (circleDensityLift o' (retainedCircleWeight ψ χ
            (fun n j => exactPassageCoeff m (H n) A j) n (h+k*(Q:ℤ))))
          n ((h+k*(Q:ℤ):ℤ):ℝ) t) a-
        foldCircleDensity (fineResidueKernel (passageBranchKernel I J₀ F) Q h n) a|
        ∂AddCircle.haarAddCircle) atTop (𝓝 0) := by
  let B : ℝ × ℝ → ℂ := fun p => A₀ (p.2 : UnitAddCircle) p.1
  let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) B ψ₀
  change ∃ S, _
  obtain ⟨hF,hcF,ε,hε,hz⟩ := exact_cutoff_weight_regular hm hR hV hdV hAr
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hψ₀ hcψ₀ h0
  have hKA : ∀ p : ℝ × ℝ, B p ≠ 0 → p.1 ∈ Icc l u :=
    fun p hp => Ioc_subset_Icc_self (hsupp _ hp)
  have hsF : tsupport F ⊆ I ×ˢ univ := by
    intro p hp
    exact ⟨(hsψ₀ (stationaryCutoffLift_support (continuous_const.mul hV.continuous)
      isCompact_Icc hKA hp).1).2,mem_univ _⟩
  obtain ⟨S,hSN,hST,ht⟩ := exact_passage_unfolded_spectral_limit hm hH hA hA₀ hAc hAd hAr
    hsupp hlo huo hlu hR hPr hV hPV hdV h0 hHc hAcont hδt hJ hIo hinj hd hj hJe hψ₀ hcψ₀
    hsψ₀ heψ hψc hχc hcχ hzχ hψ hχ hχW hQ h
  refine ⟨S,hSN,hST,?_⟩
  exact retained_circle_of_unfolded_limit hJ hIo hinj hd hF hcF hsF hε hz hψc hχc
    (fun n j => continuous_exactPassageCoeff (hHc n) hAcont j) o' hQ h S hSN ht

end ThreeTorus

end

end

end

end

end

end OAI
end

theorem solution : type_of% @OAI.ThreeTorus.exact_passage_circle_spectral_limit_oai := @OAI.ThreeTorus.exact_passage_circle_spectral_limit_oai
