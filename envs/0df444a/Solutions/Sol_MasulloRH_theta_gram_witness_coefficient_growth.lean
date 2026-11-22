-- Prove2me | solution 1 for MasulloRH.theta_gram_witness_coefficient_growth
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T23:47:24.672577+00:00
-- url     : https://prove2.me/submissions/10f471fb-0bcf-4a34-a863-82dfb44c770f

import Mathlib
import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Theorems.Thm_MasulloRH_dyadic_gaussian_theta_mellin
import Theorems.Thm_MasulloRH_finite_theta_residual_tail_bound
import Theorems.Thm_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
import Theorems.Thm_Zeta23_RvM_zeta_growth_right_at


/-!
# A necessary coefficient-mass bound for the actual theta witnesses

The Mellin/logarithmic change of variables and normalized Gaussian transform
are adapted, with attribution, from marozols' accepted proof of theorem
8481aa5d-a121-4938-8de2-17c814da37b2, saved as
prove2me_round2/gram_identity_solution.lean. Only its elementary helper proofs
are extracted here; the public theorem itself is not imported. The pointwise
frequency/coefficient inequality and the scheduled high-frequency obstruction
are new consequences developed in round six. No RH or Mertens assumption is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
open MasulloRH.GaussianApproximation

namespace MasulloRH.Round6Gram
noncomputable section

def thetaTransform (s : ℂ) : ℂ :=
  (1-(2:ℂ)^(-s))*(1-(2:ℂ)^(1-s))*completedRiemannZeta s

def coefficientMass {m : ℕ} (c : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ) : ℝ :=
  ∑ i, ‖a i‖ * Real.exp (c*y i)

theorem residual_integrable {m : ℕ} (T c b : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ)
    (hT : 0 ≤ T) (hleft : 0 < c-b) (hright : c+b < 1) :
    Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖^2) := by
  let R : ℝ := 1/2 + ∑ i, |y i - Real.log 2|
  have hR : (1/2:ℝ) ≤ R := by
    dsimp [R]
    have hsum : 0 ≤ ∑ i, |y i - Real.log 2| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith
  have hshift (i : Fin m) : |y i - Real.log 2| ≤ R := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
      abs_nonneg (y j-Real.log 2)) (Finset.mem_univ i)
    dsimp [R]
    linarith
  exact (MasulloRH.finite_theta_residual_tail_bound m T c b R a y hT hR hleft hright hshift).1

private theorem theta_measurable : Measurable theta := by
  unfold theta
  apply Measurable.tsum
  intro k
  fun_prop

private theorem residual_measurable {m : ℕ} (T : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ) :
    Measurable (residual T a y) := by
  unfold GaussianApproximation.residual
  apply Measurable.sub
  · unfold pulse
    fun_prop
  · apply Finset.measurable_sum
    intro i hi
    exact measurable_const.mul (theta_measurable.comp (measurable_id.sub measurable_const))

private lemma hasMellin_log_iff (F : ℝ → ℂ) (s r : ℂ) :
    HasMellin F s r ↔ Integrable (fun x : ℝ => Complex.exp (s*x) * F (Real.exp x)) ∧
      (∫ x : ℝ, Complex.exp (s*x) * F (Real.exp x)) = r := by
  have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have him : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  have he (x : ℝ) : |Real.exp x| • (((Real.exp x : ℝ):ℂ)^(s-1) • F (Real.exp x)) =
      Complex.exp (s*x)*F (Real.exp x) := by
    rw [abs_of_pos (Real.exp_pos _),Complex.real_smul,smul_eq_mul,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp,Complex.ofReal_exp,←mul_assoc,←Complex.exp_add]
    congr 2; ring
  unfold HasMellin MellinConvergent mellin
  rw [← him,integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn]
  simp only [integrableOn_univ, setIntegral_univ, he]


theorem theta_laplace (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    Integrable (fun x : ℝ => Complex.exp (s*x)*theta x) ∧
    (∫ x : ℝ, Complex.exp (s*x)*theta x) = thetaTransform s := by
  obtain ⟨g,hg,_,_,hm,_⟩ := MasulloRH.dyadic_gaussian_theta_mellin
  let F (t : ℝ) := ∑' k : ℤ, g ((k:ℝ)*t)
  have h := (hasMellin_log_iff F s (thetaTransform s)).1 (hm s h0 h1).1
  have he (x : ℝ) : F (Real.exp x) = theta x := by simp only [F,theta,hg]
  simpa only [he] using h

theorem theta_shift_laplace (s : ℂ) (y : ℝ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    Integrable (fun x : ℝ => Complex.exp (s*x)*theta (x-y)) ∧
    (∫ x : ℝ, Complex.exp (s*x)*theta (x-y)) = Complex.exp (s*y)*thetaTransform s := by
  obtain ⟨hi,he⟩ := theta_laplace s h0 h1
  let H (x : ℝ) := Complex.exp (s*x)*theta x
  have h (x : ℝ) : Complex.exp (s*x)*theta (x-y) = Complex.exp (s*y)*H (x-y) := by
    dsimp [H]
    rw [←mul_assoc,←Complex.exp_add]
    push_cast
    congr 2
    ring
  simp_rw [h]
  refine ⟨(hi.comp_sub_right y).const_mul _,?_⟩
  rw [integral_const_mul,integral_sub_right_eq_self,he]

def pulseValue (T : ℝ) (s : ℂ) : ℂ := Complex.exp (s^2/(4*((T+1:ℝ):ℂ)^2))

private lemma pulse_laplace_form (T : ℝ) (s : ℂ) (x : ℝ) :
    Complex.exp (s*x) * pulse T x = (((T+1)/Real.sqrt Real.pi : ℝ):ℂ) *
      Complex.exp (-(((T+1)^2 : ℝ):ℂ)*x^2 + s*x + 0) := by
  unfold pulse
  rw [add_zero, Complex.exp_add]
  push_cast
  ring_nf

lemma pulse_laplace_integrable {T : ℝ} (hT : 0 ≤ T) (s : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (s*x) * pulse T x) := by
  simp_rw [pulse_laplace_form]
  exact (integrable_cexp_quadratic (b:=(((T+1)^2:ℝ):ℂ)) (by norm_cast; positivity) s 0).const_mul _

private lemma normalizing_root {a : ℝ} (ha : 0 < a) :
    (((Real.pi/a^2:ℝ):ℂ) ^ (1/2:ℂ)) = ((Real.sqrt Real.pi/a : ℝ):ℂ) := by
  have hr : (((1/2:ℝ):ℂ)) = (1/2:ℂ) := by norm_num
  rw [← hr, ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow,
    Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq ha.le]

lemma pulse_laplace {T : ℝ} (hT : 0 ≤ T) (s : ℂ) :
    (∫ x : ℝ, Complex.exp (s*x) * pulse T x) = pulseValue T s := by
  simp_rw [pulse_laplace_form]
  rw [integral_const_mul, integral_cexp_quadratic (show (-(((T+1)^2 : ℝ):ℂ)).re < 0 by
    simp only [Complex.neg_re, Complex.ofReal_re]; nlinarith), neg_neg]
  rw [← Complex.ofReal_div, normalizing_root (show 0 < T+1 by linarith), ← mul_assoc,
    ← Complex.ofReal_mul]
  have hr : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have ha : T+1 ≠ 0 := by linarith
  rw [show (T+1)/Real.sqrt Real.pi*(Real.sqrt Real.pi/(T+1))=1 by field_simp,
    Complex.ofReal_one, one_mul]
  unfold pulseValue
  congr 1
  rw [zero_sub, mul_neg, div_neg, neg_neg, Complex.ofReal_pow]


lemma pulseValue_norm (T : ℝ) (s : ℂ) :
    ‖pulseValue T s‖ = Real.exp ((s.re^2-s.im^2)/(4*(T+1)^2)) := by
  rw [pulseValue,Complex.norm_exp]
  congr 1
  have he : (4:ℂ)*((T+1:ℝ):ℂ)^2 = ((4*(T+1)^2:ℝ):ℂ) := by push_cast; rfl
  rw [he,Complex.div_ofReal_re,pow_two,Complex.mul_re]
  ring

private theorem exp_abs_integral {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-2*b*|x|)) ∧
    (∫ x : ℝ, Real.exp (-2*b*|x|)) = 1/b := by
  have hp := integrableOn_exp_mul_Ioi (a := -2*b) (by linarith) 0
  have hm := integrableOn_exp_mul_Iic (a := 2*b) (by linarith) 0
  have h := Integrable.piecewise (s := Ioi (0:ℝ)) measurableSet_Ioi hp
    (by simpa only [compl_Ioi] using hm)
  constructor
  · apply h.congr
    filter_upwards [] with x
    by_cases hx : 0 < x
    · simp [Set.piecewise,hx,abs_of_pos hx]
    · have hx' : x ≤ 0 := le_of_not_gt hx
      simp [Set.piecewise,hx,abs_of_nonpos hx']
  · rw [integral_comp_abs (f := fun x : ℝ => Real.exp (-2*b*x)),
      integral_exp_mul_Ioi (show -2*b < 0 by linarith) 0]
    simp only [mul_zero,Real.exp_zero]
    field_simp
    <;> ring

/-- Exact central-line evaluation constant: squared norm of the dual vector is `1/b`. -/
theorem center_laplace_bound (q : ℝ → ℂ) (hq : AEStronglyMeasurable q volume)
    (c b : ℝ) (hb : 0 < b) (s : ℂ) (hs : s.re = c)
    (hJ : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖q x‖^2)) :
    Integrable (fun x : ℝ => Complex.exp (s*(x:ℝ))*q x) ∧
    ‖∫ x : ℝ, Complex.exp (s*(x:ℝ))*q x‖^2 ≤ energy c b q / b := by
  let A (x : ℝ) := Real.exp (c*x+b*|x|)*‖q x‖
  let B (x : ℝ) := Real.exp (-b*|x|)
  have hA2 (x : ℝ) : A x^2 = Real.exp (2*c*x+2*b*|x|)*‖q x‖^2 := by
    simp only [A,mul_pow,←Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hB2 (x : ℝ) : B x^2 = Real.exp (-2*b*|x|) := by
    dsimp only [B]
    rw [←Real.exp_nat_mul]
    congr 1; push_cast; ring
  have hAmeas : AEStronglyMeasurable A volume :=
    (show Continuous (fun x : ℝ => Real.exp (c*x+b*|x|)) by fun_prop).aestronglyMeasurable.mul hq.norm
  have hA : MemLp A 2 volume := (memLp_two_iff_integrable_sq hAmeas).mpr
    (by simpa only [hA2] using hJ)
  obtain ⟨hK,hKi⟩ := exp_abs_integral hb
  have hB : MemLp B 2 volume := (memLp_two_iff_integrable_sq (by dsimp [B]; fun_prop)).mpr
    (by simpa only [hB2] using hK)
  have hAB := hA.integrable_mul hB
  have hnorm (x : ℝ) : ‖Complex.exp (s*x)*q x‖ = A x*B x := by
    simp only [A,B,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero,hs]
    calc
      _ = (Real.exp (c*x+b*|x|)*Real.exp (-b*|x|))*‖q x‖ := by
        rw [←Real.exp_add]; congr 2; ring
      _ = _ := by ring
  refine ⟨hAB.mono'
    ((show Continuous (fun x : ℝ => Complex.exp (s*x)) by fun_prop).aestronglyMeasurable.mul hq)
    (Eventually.of_forall fun x => (hnorm x).le),?_⟩
  have hJ0 : 0 ≤ energy c b q := integral_nonneg (fun x => by positivity)
  have hho := integral_mul_le_Lp_mul_Lq_of_nonneg (μ:=volume) (p:=2) (q:=2)
    (by norm_num [Real.holderConjugate_iff]) (f:=A) (g:=B)
    (Eventually.of_forall fun x => mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
    (Eventually.of_forall fun x => Real.exp_nonneg _) (by simpa using hA) (by simpa using hB)
  have hI : ‖∫ x : ℝ, Complex.exp (s*x)*q x‖ ≤ Real.sqrt (energy c b q)*Real.sqrt (1/b) := by
    apply (norm_integral_le_integral_norm _).trans
    simp only [hnorm]
    simpa only [Real.rpow_two,hA2,hB2,hKi,←Real.sqrt_eq_rpow,energy] using hho
  calc
    _ ≤ (Real.sqrt (energy c b q)*Real.sqrt (1/b))^2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hI
    _ = energy c b q / b := by
      rw [mul_pow,Real.sq_sqrt hJ0,Real.sq_sqrt (by positivity)]
      ring

theorem residual_laplace {m : ℕ} (T : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ)
    (hT : 0 ≤ T) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    (∫ x : ℝ, Complex.exp (s*x)*residual T a y x) =
      pulseValue T s - (∑ i, a i*Complex.exp (s*y i))*thetaTransform s := by
  have hf (i : Fin m) : Integrable (fun x : ℝ => a i*(Complex.exp (s*x)*theta (x-y i))) :=
    (theta_shift_laplace s (y i) h0 h1).1.const_mul _
  have he (x : ℝ) : Complex.exp (s*x)*residual T a y x =
      Complex.exp (s*x)*pulse T x - ∑ i, a i*(Complex.exp (s*x)*theta (x-y i)) := by
    simp only [GaussianApproximation.residual,mul_sub,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [he]
  rw [integral_sub (pulse_laplace_integrable hT s) (integrable_finsetSum _ (fun i _ => hf i)),
    integral_finsetSum _ (fun i _ => hf i),pulse_laplace hT s]
  simp only [integral_const_mul,(theta_shift_laplace s _ h0 h1).2]
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A necessary finite-frequency inequality for the literal theta and pulse.
The endpoint weight is unchanged and all integrability is proved from the
actual finite-residual tail theorem. -/
theorem frequency_mass_bound {m : ℕ} (T c b t : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ)
    (hT : 0 ≤ T) (hb : 0 < b) (hleft : 0 < c-b) (hright : c+b < 1) :
    Real.exp ((c^2-t^2)/(4*(T+1)^2)) ≤
      Real.sqrt (energy c b (residual T a y)/b) +
        coefficientMass c a y * ‖thetaTransform ((c:ℂ)+(t:ℂ)*Complex.I)‖ := by
  let s : ℂ := (c:ℂ)+(t:ℂ)*Complex.I
  have hs : s.re = c := by simp [s]
  have hs0 : 0 < s.re := by rw [hs]; linarith
  have hs1 : s.re < 1 := by rw [hs]; linarith
  have hJ := residual_integrable T c b a y hT hleft hright
  have hLap := (center_laplace_bound (residual T a y)
    (residual_measurable T a y).aestronglyMeasurable c b hb s hs hJ).2
  have hE0 : 0 ≤ energy c b (residual T a y)/b := by
    apply div_nonneg _ hb.le
    exact integral_nonneg (fun x => by positivity)
  have hsmall : ‖∫ x : ℝ, Complex.exp (s*x)*residual T a y x‖ ≤
      Real.sqrt (energy c b (residual T a y)/b) := by
    nlinarith [Real.sq_sqrt hE0,Real.sqrt_nonneg (energy c b (residual T a y)/b),
      norm_nonneg (∫ x : ℝ, Complex.exp (s*x)*residual T a y x)]
  have hmass : ‖∑ i, a i*Complex.exp (s*y i)‖ ≤ coefficientMass c a y := by
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro i hi
    simp [norm_mul,Complex.norm_exp,Complex.mul_re,hs,coefficientMass]
  have hn := norm_add_le (pulseValue T s - (∑ i, a i*Complex.exp (s*y i))*thetaTransform s)
    ((∑ i, a i*Complex.exp (s*y i))*thetaTransform s)
  rw [sub_add_cancel,←residual_laplace T a y hT s hs0 hs1,norm_mul] at hn
  have hnormp : ‖pulseValue T s‖ = Real.exp ((c^2-t^2)/(4*(T+1)^2)) := by
    rw [pulseValue_norm]
    simp [s]
  rw [hnormp] at hn
  exact hn.trans (add_le_add hsmall (mul_le_mul_of_nonneg_right hmass (norm_nonneg _)))


/-- A frequency growing faster than linearly, selected to keep the Gaussian
transform above the square-root energy error. -/
def scheduledFrequency (n : ℕ) : ℝ :=
  ((n:ℝ)+1)*Real.sqrt (2*Real.log ((n:ℝ)+1))

private theorem exp_neg_half_log {k : ℝ} (hk : 0 < k) :
    Real.exp (-Real.log k/2) = 1/Real.sqrt k := by
  have he : Real.exp (Real.log k/2) = Real.sqrt k := by
    have hs : Real.exp (Real.log k/2)^2 = k := by
      rw [←Real.exp_nat_mul]
      norm_num
      rw [show 2*(Real.log k/2)=Real.log k by ring,Real.exp_log hk]
    nlinarith [Real.sq_sqrt hk.le,Real.exp_pos (Real.log k/2),Real.sqrt_nonneg k]
  rw [show -Real.log k/2 = -(Real.log k/2) by ring,Real.exp_neg,he,one_div]

/-- Every actual-energy witness for the canonical schedule has a definite
weighted coefficient mass after multiplication by its theta transform at
`scheduledFrequency n`. Rational coefficients and shifts are retained. -/
theorem scheduled_rational_witness_mass_bound (n m : ℕ)
    (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ)
    (hE : energy (3/4) (1/4-1/(16*((n:ℝ)+1)))
      (residual n (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I)
        (fun i => (y i:ℝ))) < 1/(32*((n:ℝ)+1))) :
    1/(2*Real.sqrt ((n:ℝ)+1)) <
      (∑ i, ‖((a i).1:ℂ)+((a i).2:ℂ)*Complex.I‖ * Real.exp ((3/4)*(y i:ℝ))) *
        ‖thetaTransform ((3/4:ℂ)+(scheduledFrequency n:ℂ)*Complex.I)‖ := by
  let k : ℝ := (n:ℝ)+1
  let b : ℝ := 1/4-1/(16*k)
  let aC : Fin m → ℂ := fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I
  let yR : Fin m → ℝ := fun i => (y i:ℝ)
  let E : ℝ := energy (3/4) b (residual n aC yR)
  have hk1 : 1 ≤ k := by
    dsimp [k]
    have hn := Nat.cast_nonneg (α:=ℝ) n
    linarith
  have hk : 0 < k := by linarith
  have hd : 0 < 1/(16*k) := by positivity
  have hdu : 1/(16*k) ≤ (1/16:ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hbl : (1/8:ℝ) ≤ b := by dsimp [b]; linarith
  have hleft : 0 < (3/4:ℝ)-b := by dsimp [b]; linarith
  have hright : (3/4:ℝ)+b < 1 := by dsimp [b]; linarith
  change E < 1/(32*k) at hE
  have hE0 : 0 ≤ E := integral_nonneg (fun x => by positivity)
  have hdiv : E/b < 1/(4*k) := by
    rw [div_lt_iff₀ hb]
    apply hE.trans_le
    calc
      1/(32*k) = (1/(4*k))*(1/8) := by field_simp; ring
      _ ≤ (1/(4*k))*b := mul_le_mul_of_nonneg_left hbl (by positivity)
  have hq : 0 < 1/(2*Real.sqrt k) := by positivity
  have hq2 : (1/(2*Real.sqrt k))^2 = 1/(4*k) := by
    rw [div_pow,mul_pow,Real.sq_sqrt hk.le]
    norm_num
  have hsmall : Real.sqrt (E/b) < 1/(2*Real.sqrt k) := by
    have hs := Real.sq_sqrt (div_nonneg hE0 hb.le)
    nlinarith [Real.sqrt_nonneg (E/b)]
  have ht : (scheduledFrequency n)^2 = 2*k^2*Real.log k := by
    dsimp [scheduledFrequency]
    change (k*Real.sqrt (2*Real.log k))^2 = _
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (by norm_num) (Real.log_nonneg hk1))]
    ring
  have hp : 1/Real.sqrt k ≤
      Real.exp (((3/4:ℝ)^2-(scheduledFrequency n)^2)/(4*k^2)) := by
    rw [←exp_neg_half_log hk,Real.exp_le_exp,le_div_iff₀ (by positivity)]
    rw [ht]
    nlinarith
  have hf := frequency_mass_bound (n:ℝ) (3/4) b (scheduledFrequency n) aC yR
    (Nat.cast_nonneg n) hb hleft hright
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat] at hf
  change Real.exp (((3/4:ℝ)^2-(scheduledFrequency n)^2)/(4*k^2)) ≤
    Real.sqrt (E/b) + coefficientMass (3/4) aC yR *
      ‖thetaTransform ((3/4:ℂ)+(scheduledFrequency n:ℂ)*Complex.I)‖ at hf
  have hh : 1/Real.sqrt k = 2*(1/(2*Real.sqrt k)) := by field_simp
  change 1/(2*Real.sqrt k) < coefficientMass (3/4) aC yR *
    ‖thetaTransform ((3/4:ℂ)+(scheduledFrequency n:ℂ)*Complex.I)‖
  nlinarith

end
end MasulloRH.Round6Gram




/-!
# Coefficient growth forced by the canonical Gram energy schedule

This combines the exact finite-frequency obstruction with two independently
proved classical estimates: polynomial zeta growth in a right half-plane and
the standard exponential gamma bound on a vertical strip. There is no RH,
Mertens, density, or automatic moment-vanishing hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set MeasureTheory Filter
open scoped Topology BigOperators
open MasulloRH.GaussianApproximation

namespace MasulloRH.Round6Gram
noncomputable section

theorem theta_transform_center_decay :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧ ∀ t : ℝ, 2 ≤ |t| →
      ‖thetaTransform ((3/4:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        C*(1+|t|)^M*Real.exp (-(Real.pi/4)*|t|) := by
  obtain ⟨A,N,hG⟩ :=
    Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
      (3/8) (3/8)
  let A' : ℝ := max A 0 + 1
  have hA' : 0 < A' := by dsimp [A']; positivity
  have hAA : A ≤ A' := by dsimp [A']; linarith [le_max_left A 0]
  let D₁ : ℝ := 1+(2:ℝ)^(-(3/4:ℝ))
  let D₂ : ℝ := 1+(2:ℝ)^(1/4:ℝ)
  let P : ℝ := Real.pi^(-(3/8:ℝ))
  let C : ℝ := D₁*D₂*P*A'*20
  have hD₁ : 0 < D₁ := by dsimp [D₁]; positivity
  have hD₂ : 0 < D₂ := by dsimp [D₂]; positivity
  have hP : 0 < P := Real.rpow_pos_of_pos Real.pi_pos _
  refine ⟨C,N+1,by dsimp [C]; positivity,?_⟩
  intro t ht
  let s : ℂ := (3/4:ℂ)+(t:ℂ)*Complex.I
  have hs : s.re = 3/4 := by simp [s]
  have hsi : s.im = t := by simp [s]
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hs] at this
  have hs2 : (s/2).re = 3/8 := by rw [Complex.div_ofNat_re,hs]; norm_num
  have hsi2 : |(s/2).im| = |t|/2 := by
    rw [Complex.div_ofNat_im,hsi,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hG₀ := (hG (s/2) hs2.ge hs2.le (by rw [hsi2]; linarith)).1
  rw [hsi2] at hG₀
  have hGamma : ‖Complex.Gamma (s/2)‖ ≤
      A'*(1+|t|)^N*Real.exp (-(Real.pi/4)*|t|) := by
    calc
      _ ≤ A*(1+|t|/2)^N*Real.exp (-(Real.pi/2)*(|t|/2)) := hG₀
      _ ≤ A'*(1+|t|/2)^N*Real.exp (-(Real.pi/2)*(|t|/2)) := by gcongr
      _ ≤ A'*(1+|t|)^N*Real.exp (-(Real.pi/4)*|t|) := by
        rw [show -(Real.pi/2)*(|t|/2)=-(Real.pi/4)*|t| by ring]
        gcongr
        linarith [abs_nonneg t]
  have hd : 1 ≤ ‖s-1‖ := by
    have hi := Complex.abs_im_le_norm (s-1)
    simp only [Complex.sub_im,Complex.one_im,sub_zero,hsi] at hi
    linarith
  have hz₀ := Zeta23.RvM.zeta_growth_right_at s (by rw [hs]; norm_num) hd
  rw [hsi,Real.rpow_one] at hz₀
  have hz : ‖riemannZeta s‖ ≤ 20*(1+|t|) := by
    nlinarith [abs_nonneg t]
  have h₂ (z : ℂ) : ‖(2:ℂ)^z‖ = (2:ℝ)^z.re := by
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) z
  have hf₁ : ‖1-(2:ℂ)^(-s)‖ ≤ D₁ := by
    have h := norm_sub_le (1:ℂ) ((2:ℂ)^(-s))
    simpa only [norm_one,h₂,Complex.neg_re,hs,D₁] using h
  have hf₂ : ‖1-(2:ℂ)^(1-s)‖ ≤ D₂ := by
    have h := norm_sub_le (1:ℂ) ((2:ℂ)^(1-s))
    simpa only [norm_one,h₂,Complex.sub_re,Complex.one_re,hs,
      show (1:ℝ)-3/4=1/4 by norm_num,D₂] using h
  have hpi : ‖(Real.pi:ℂ)^(-s/2)‖ = P := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    rw [Complex.div_ofNat_re,Complex.neg_re,hs]
    norm_num
  have hcomp : completedRiemannZeta s = Complex.Gammaℝ s*riemannZeta s := by
    have h := (eq_div_iff (Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num))).mp
      (riemannZeta_def_of_ne_zero hs0)
    rw [←h,mul_comm]
  have hcnorm : ‖completedRiemannZeta s‖ = P*‖Complex.Gamma (s/2)‖*‖riemannZeta s‖ := by
    rw [hcomp,Complex.Gammaℝ_def,norm_mul,norm_mul,hpi]
  change ‖thetaTransform s‖ ≤ _
  calc
    _ = ‖1-(2:ℂ)^(-s)‖*‖1-(2:ℂ)^(1-s)‖*
        (P*‖Complex.Gamma (s/2)‖*‖riemannZeta s‖) := by
      rw [thetaTransform,norm_mul,norm_mul,hcnorm]
    _ ≤ D₁*D₂*(P*(A'*(1+|t|)^N*Real.exp (-(Real.pi/4)*|t|))*(20*(1+|t|))) := by
      gcongr
    _ = C*(1+|t|)^(N+1)*Real.exp (-(Real.pi/4)*|t|) := by
      dsimp [C]
      rw [pow_succ]
      ring

theorem scheduled_frequency_large (n : ℕ) (hn : 2 ≤ n) : 2 ≤ scheduledFrequency n := by
  have hk : (3:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast (show 3 ≤ n+1 by omega)
  have hlog : 1 ≤ Real.log ((n:ℝ)+1) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log ((n:ℝ)+1) := by
        apply Real.log_le_log (Real.exp_pos 1)
        have he := Real.exp_one_lt_d9
        linarith
  have hs := Real.sq_sqrt (show 0 ≤ 2*Real.log ((n:ℝ)+1) by linarith)
  have hroot : 1 ≤ Real.sqrt (2*Real.log ((n:ℝ)+1)) := by
    nlinarith [Real.sqrt_nonneg (2*Real.log ((n:ℝ)+1))]
  dsimp [scheduledFrequency]
  nlinarith

/-- A uniform necessary growth bound for every rational witness at every
integer height at least two. The constants are independent of the number of
translates, all coefficients, all shifts and the height. -/
theorem scheduled_rational_witness_mass_growth :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧ ∀ (n m : ℕ), 2 ≤ n →
      ∀ (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      energy (3/4) (1/4-1/(16*((n:ℝ)+1)))
        (residual n (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I)
          (fun i => (y i:ℝ))) < 1/(32*((n:ℝ)+1)) →
      Real.exp ((Real.pi/4)*scheduledFrequency n) /
        (2*C*Real.sqrt ((n:ℝ)+1)*(1+scheduledFrequency n)^M) <
      ∑ i, ‖((a i).1:ℂ)+((a i).2:ℂ)*Complex.I‖*Real.exp ((3/4)*(y i:ℝ)) := by
  obtain ⟨C,M,hC,hdec⟩ := theta_transform_center_decay
  refine ⟨C,M,hC,?_⟩
  intro n m hn a y hE
  let τ : ℝ := scheduledFrequency n
  let k : ℝ := (n:ℝ)+1
  let L : ℝ := ∑ i, ‖((a i).1:ℂ)+((a i).2:ℂ)*Complex.I‖*Real.exp ((3/4)*(y i:ℝ))
  have hτ : 0 ≤ τ := (show (0:ℝ) ≤ 2 by norm_num).trans (scheduled_frequency_large n hn)
  have hk : 0 < k := by dsimp [k]; positivity
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => by positivity)
  have hd := hdec τ (by rw [abs_of_nonneg hτ]; exact scheduled_frequency_large n hn)
  rw [abs_of_nonneg hτ] at hd
  have hm := scheduled_rational_witness_mass_bound n m a y hE
  change 1/(2*Real.sqrt k) < L*‖thetaTransform ((3/4:ℂ)+(τ:ℂ)*Complex.I)‖ at hm
  have hsmall : 1/(2*Real.sqrt k) < L*(C*(1+τ)^M*Real.exp (-(Real.pi/4)*τ)) :=
    hm.trans_le (mul_le_mul_of_nonneg_left hd hL)
  change Real.exp ((Real.pi/4)*τ)/(2*C*Real.sqrt k*(1+τ)^M) < L
  rw [div_lt_iff₀ (by positivity)]
  calc
    _ = (1/(2*Real.sqrt k))*(2*Real.sqrt k*Real.exp ((Real.pi/4)*τ)) := by
      field_simp
    _ < (L*(C*(1+τ)^M*Real.exp (-(Real.pi/4)*τ)))*
        (2*Real.sqrt k*Real.exp ((Real.pi/4)*τ)) :=
      mul_lt_mul_of_pos_right hsmall (by positivity)
    _ = L*(2*C*Real.sqrt k*(1+τ)^M) := by
      rw [show -(Real.pi/4)*τ = -((Real.pi/4)*τ) by ring,Real.exp_neg]
      field_simp

end
end MasulloRH.Round6Gram



/-!
# Exact augmented Gram form of the coefficient-growth obstruction

Finite Gram integration algebra below is extracted with attribution from
marozols' accepted proof 5b2cbfbc-22d8-4073-bb0e-dbecd2699cb3 of theorem
8481aa5d-a121-4938-8de2-17c814da37b2. No helper from that public theorem is
imported. Column integrability is proved here from the public actual-tail
estimate already used by the coefficient-mass core.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
open MasulloRH.GaussianApproximation

namespace MasulloRH.Round6Gram
noncomputable section

/-- The positive weight used to control Laplace evaluation in the open strip. -/
def gramWeight (c b x : ℝ) := Real.exp (2*c*x+2*b*|x|)

def gramEntry (c b : ℝ) (f g : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, (gramWeight c b x : ℂ) * conj (f x) * g x

theorem gramEntry_integrable (c b : ℝ) {f g : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hF : Integrable (fun x => gramWeight c b x * ‖f x‖^2))
    (hG : Integrable (fun x => gramWeight c b x * ‖g x‖^2)) :
    Integrable (fun x : ℝ => (gramWeight c b x : ℂ)*conj (f x)*g x) := by
  apply ((hF.add hG).const_mul (1/2:ℝ)).mono'
  · exact ((show Continuous (fun x : ℝ => (gramWeight c b x : ℂ)) by unfold gramWeight; fun_prop).aestronglyMeasurable.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable hf)).mul hg
  · apply Filter.Eventually.of_forall
    intro x
    have hw : 0 ≤ gramWeight c b x := (Real.exp_pos _).le
    simp only [norm_mul, Complex.norm_conj,Complex.norm_real,Real.norm_of_nonneg hw,Pi.add_apply]
    nlinarith [mul_nonneg hw (sq_nonneg (‖f x‖-‖g x‖))]
private theorem gram_pointwise {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ℂ) (a u : ι → ℂ) (b v : κ → ℂ) :
    w * conj (∑ i, a i*u i) * (∑ j, b j*v j) =
      ∑ i, ∑ j, (conj (a i)*b j) * (w*conj (u i)*v j) := by
  calc
    _ = (∑ i, w*(conj (a i)*conj (u i))) * (∑ j, b j*v j) := by
      congr 1
      rw [map_sum, Finset.mul_sum]
      simp only [map_mul]
    _ = ∑ i, (w*(conj (a i)*conj (u i))) * (∑ j, b j*v j) := Finset.sum_mul ..
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Hermitian inner product of finite linear combinations is the corresponding matrix form. -/
theorem gramEntry_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c b : ℝ) (f : ι → ℝ → ℂ) (g : κ → ℝ → ℂ) (a : ι→ℂ) (d : κ→ℂ)
    (hf : ∀ i, AEStronglyMeasurable (f i) volume) (hg : ∀ j, AEStronglyMeasurable (g j) volume)
    (hF : ∀ i, Integrable (fun x => gramWeight c b x * ‖f i x‖^2))
    (hG : ∀ j, Integrable (fun x => gramWeight c b x * ‖g j x‖^2)) :
    Integrable (fun x : ℝ => (gramWeight c b x:ℂ) * conj (∑ i, a i*f i x) * (∑ j, d j*g j x)) ∧
    gramEntry c b (fun x => ∑ i, a i*f i x) (fun x => ∑ j, d j*g j x) =
      ∑ i, ∑ j, conj (a i)*d j*gramEntry c b (f i) (g j) := by
  let K (i : ι) (j : κ) (x : ℝ) := (conj (a i)*d j)*((gramWeight c b x:ℂ)*conj (f i x)*g j x)
  have hK (i j) : Integrable (K i j) :=
    (gramEntry_integrable c b (hf i) (hg j) (hF i) (hG j)).const_mul _
  have he (x : ℝ) : (gramWeight c b x:ℂ)*conj (∑ i, a i*f i x)*(∑ j, d j*g j x) =
      ∑ i, ∑ j, K i j x := gram_pointwise _ _ _ _ _
  have hrow (i) : Integrable (fun x => ∑ j, K i j x) := integrable_finsetSum _ (fun j _ => hK i j)
  constructor
  · simp only [he]
    exact integrable_finsetSum _ (fun i _ => hrow i)
  · unfold gramEntry
    simp only [he]
    rw [integral_finsetSum _ (fun i _ => hrow i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hK i j)]
    exact Finset.sum_congr rfl (fun j _ => integral_const_mul ..)

/-- Weighted Gram energy is the real part of the Hermitian quadratic form. -/
theorem finite_gram_energy {ι : Type*} [Fintype ι] (c b : ℝ) (f : ι→ℝ→ℂ) (a : ι→ℂ)
    (hf : ∀ i, AEStronglyMeasurable (f i) volume)
    (hF : ∀ i, Integrable (fun x => gramWeight c b x * ‖f i x‖^2)) :
    AEStronglyMeasurable (fun x => ∑ i, a i*f i x) volume ∧
      Integrable (fun x : ℝ => gramWeight c b x * ‖∑ i, a i*f i x‖^2) ∧
      (∫ x : ℝ, gramWeight c b x * ‖∑ i, a i*f i x‖^2) =
        (∑ i, ∑ j, conj (a i)*a j*gramEntry c b (f i) (f j)).re := by
  obtain ⟨hint,hid⟩ := gramEntry_sum_sum c b f f a a hf hf hF hF
  let S (x : ℝ) := ∑ i, a i*f i x
  have he (x : ℝ) : ((gramWeight c b x:ℂ)*conj (S x)*S x).re = gramWeight c b x * ‖S x‖^2 := by
    rw [mul_assoc,Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hint' : Integrable (fun x : ℝ => gramWeight c b x * ‖S x‖^2) := by
    have hreal : Integrable (fun x : ℝ => ((gramWeight c b x:ℂ)*conj (S x)*S x).re) := hint.re
    simpa only [he] using hreal
  refine ⟨Finset.aestronglyMeasurable_fun_sum _ (fun i _ => aestronglyMeasurable_const.mul (hf i)),hint',?_⟩
  rw [← hid]
  change (∫ x : ℝ, gramWeight c b x * ‖S x‖^2) = (∫ x : ℝ, (gramWeight c b x:ℂ)*conj (S x)*S x).re
  have hir : (∫ x : ℝ, ((gramWeight c b x:ℂ)*conj (S x)*S x).re) =
      (∫ x : ℝ, (gramWeight c b x:ℂ)*conj (S x)*S x).re := integral_re hint
  simpa only [he] using hir

/-- Signed residual form. Index zero is the target, and the remaining entries are the trial
columns. Its quadratic form, including all cross terms, is the exact residual energy. -/
theorem finite_gram_residual {m : ℕ} (c b : ℝ) (h : ℝ→ℂ) (f : Fin m→ℝ→ℂ) (a : Fin m→ℂ)
    (hh : AEStronglyMeasurable h volume) (hf : ∀ i, AEStronglyMeasurable (f i) volume)
    (hH : Integrable (fun x => gramWeight c b x * ‖h x‖^2))
    (hF : ∀ i, Integrable (fun x => gramWeight c b x * ‖f i x‖^2)) :
    let v := Fin.cons h f
    let d := Fin.cons (1:ℂ) (fun j => -a j)
    AEStronglyMeasurable (fun x => h x - ∑ j, a j*f j x) volume ∧
      Integrable (fun x : ℝ => gramWeight c b x * ‖h x - ∑ j, a j*f j x‖^2) ∧
      (∫ x : ℝ, gramWeight c b x * ‖h x - ∑ j, a j*f j x‖^2) =
        (∑ i, ∑ j, conj (d i)*d j*gramEntry c b (v i) (v j)).re := by
  intro v d
  have hv (i : Fin (m+1)) : AEStronglyMeasurable (v i) volume := Fin.cases hh hf i
  have hV (i : Fin (m+1)) : Integrable (fun x => gramWeight c b x * ‖v i x‖^2) := Fin.cases hH hF i
  have hs (x : ℝ) : ∑ i, d i*v i x = h x - ∑ j, a j*f j x := by
    simp [v,d,Fin.sum_univ_succ,Finset.sum_neg_distrib,sub_eq_add_neg]
  simpa only [hs] using finite_gram_energy c b v d hv hV


private theorem pulse_energy_integrable (T c b : ℝ)
    (hT : 0 ≤ T) (hleft : 0 < c-b) (hright : c+b < 1) :
    Integrable (fun x : ℝ => gramWeight c b x*‖pulse T x‖^2) := by
  have h := residual_integrable (m:=0) T c b Fin.elim0 Fin.elim0 hT hleft hright
  simpa only [GaussianApproximation.residual,Fin.sum_univ_zero,sub_zero,gramWeight] using h

private theorem theta_energy_integrable (c b y : ℝ)
    (hleft : 0 < c-b) (hright : c+b < 1) :
    Integrable (fun x : ℝ => gramWeight c b x*‖theta (x-y)‖^2) := by
  let r : ℝ → ℂ := residual 0 (fun _ : Fin 1 => 1) (fun _ => y)
  have hP := pulse_energy_integrable 0 c b (by norm_num) hleft hright
  have hR := residual_integrable 0 c b (fun _ : Fin 1 => 1) (fun _ => y)
    (by norm_num) hleft hright
  have hm : Measurable theta := by
    unfold theta
    apply Measurable.tsum
    intro k
    fun_prop
  apply ((hP.add hR).const_mul 2).mono' (by dsimp [gramWeight]; fun_prop)
  filter_upwards [] with x
  have he : theta (x-y) = pulse 0 x-r x := by simp [r,GaussianApproximation.residual]
  have hn : ‖theta (x-y)‖ ≤ ‖pulse 0 x‖+‖r x‖ := by rw [he]; exact norm_sub_le _ _
  have hq : ‖theta (x-y)‖^2 ≤ 2*‖pulse 0 x‖^2+2*‖r x‖^2 := by
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖pulse 0 x‖-‖r x‖)]
  have hw : 0 ≤ gramWeight c b x := Real.exp_nonneg _
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  change gramWeight c b x * ‖theta (x-y)‖^2 ≤
    2*(gramWeight c b x*‖pulse 0 x‖^2+gramWeight c b x*‖r x‖^2)
  calc
    _ ≤ gramWeight c b x*(2*‖pulse 0 x‖^2+2*‖r x‖^2) :=
      mul_le_mul_of_nonneg_left hq hw
    _ = _ := by ring

/-- The exact actual augmented theta/pulse Gram matrix, with its ordinary
integrable entries, equals the canonical energy. -/
theorem actual_gram_energy {m : ℕ} (T c b : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ)
    (hT : 0 ≤ T) (hleft : 0 < c-b) (hright : c+b < 1) :
    let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse T) (fun i x => theta (x-y i))
    let d : Fin (m+1) → ℂ := Fin.cons 1 (fun i => -a i)
    energy c b (residual T a y) =
      (∑ i, ∑ j, conj (d i)*d j*
        (∫ x : ℝ, (Real.exp (2*c*x+2*b*|x|):ℂ)*conj (u i x)*u j x)).re := by
  have ht : Measurable theta := by
    unfold theta
    apply Measurable.tsum
    intro k
    fun_prop
  have hh : AEStronglyMeasurable (pulse T) volume := by unfold pulse; fun_prop
  have hf (i : Fin m) : AEStronglyMeasurable (fun x => theta (x-y i)) volume :=
    (ht.comp (measurable_id.sub measurable_const)).aestronglyMeasurable
  have h := finite_gram_residual c b (pulse T) (fun i x => theta (x-y i)) a hh hf
    (pulse_energy_integrable T c b hT hleft hright)
    (fun i => theta_energy_integrable c b (y i) hleft hright)
  simpa only [energy,GaussianApproximation.residual,gramWeight,gramEntry] using h.2.2

/-- Necessary coefficient growth for the exact rational Gram witnesses in the
cofinal leaf. This asserts no existence of those witnesses. -/
theorem scheduled_rational_gram_witness_mass_growth :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧ ∀ (n m : ℕ), 2 ≤ n →
      ∀ (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      let k : ℝ := (n:ℝ)+1
      let δ : ℝ := 1/(16*k)
      let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse n)
        (fun i x => theta (x-(y i:ℝ)))
      let d : Fin (m+1) → ℂ := Fin.cons 1
        (fun i => -(((a i).1:ℂ)+((a i).2:ℂ)*Complex.I))
      let τ : ℝ := k*Real.sqrt (2*Real.log k)
      (∑ i, ∑ j, conj (d i)*d j*
        (∫ x : ℝ, (Real.exp (2*(3/4)*x+2*(1/4-δ)*|x|):ℂ)*conj (u i x)*u j x)).re < δ/2 →
      Real.exp ((Real.pi/4)*τ)/(2*C*Real.sqrt k*(1+τ)^M) <
        ∑ i, ‖((a i).1:ℂ)+((a i).2:ℂ)*Complex.I‖*Real.exp ((3/4)*(y i:ℝ)) := by
  obtain ⟨C,M,hC,hgrowth⟩ := scheduled_rational_witness_mass_growth
  refine ⟨C,M,hC,?_⟩
  intro n m hn a y k δ u d τ hG
  let aC : Fin m → ℂ := fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I
  let yR : Fin m → ℝ := fun i => (y i:ℝ)
  have hk : 0 < k := by dsimp [k]; positivity
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hleft : 0 < (3/4:ℝ)-(1/4-δ) := by linarith
  have hright : (3/4:ℝ)+(1/4-δ) < 1 := by linarith
  have hi := actual_gram_energy (n:ℝ) (3/4) (1/4-δ) aC yR
    (Nat.cast_nonneg n) hleft hright
  have hE : energy (3/4) (1/4-δ) (residual n aC yR) < δ/2 := by
    rw [hi]
    exact hG
  have hd32 : δ/2 = 1/(32*k) := by dsimp [δ]; ring
  rw [hd32] at hE
  exact hgrowth n m hn a y hE

end
end MasulloRH.Round6Gram


theorem solution :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧ ∀ (n m : ℕ), 2 ≤ n →
      ∀ (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      let k : ℝ := (n:ℝ)+1
      let δ : ℝ := 1/(16*k)
      let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse n)
        (fun i x => theta (x-(y i:ℝ)))
      let d : Fin (m+1) → ℂ := Fin.cons 1
        (fun i => -(((a i).1:ℂ)+((a i).2:ℂ)*Complex.I))
      let τ : ℝ := k*Real.sqrt (2*Real.log k)
      (∑ i, ∑ j, conj (d i)*d j*
        (∫ x : ℝ, (Real.exp (2*(3/4)*x+2*(1/4-δ)*|x|):ℂ)*conj (u i x)*u j x)).re < δ/2 →
      Real.exp ((Real.pi/4)*τ)/(2*C*Real.sqrt k*(1+τ)^M) <
        ∑ i, ‖((a i).1:ℂ)+((a i).2:ℂ)*Complex.I‖*Real.exp ((3/4)*(y i:ℝ)) := by
  exact MasulloRH.Round6Gram.scheduled_rational_gram_witness_mass_growth

#print axioms solution
