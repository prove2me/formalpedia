-- Prove2me | solution 1 for MellinStrip.reverse_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T07:49:29.024769+00:00
-- url     : https://prove2.me/submissions/1908670b-3b83-4b38-b7b1-cf71ec7d3b80

import Mathlib

set_option autoImplicit false

open MeasureTheory FourierTransform

namespace B3Aux

def P (I : Set ℝ) (ψ : ℝ → ℂ) : Prop :=
  ∀ a ∈ I, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ, g x = (Real.exp (a * x) : ℂ) * ψ x

lemma psi_eq {a : ℝ} {ψ : ℝ → ℂ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (a * x) : ℂ) * ψ x) (x : ℝ) :
    ψ x = (Real.exp (-(a * x)) : ℂ) * g x := by
  rw [hg, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    Complex.ofReal_one, one_mul]

lemma psi_funext {a : ℝ} {ψ : ℝ → ℂ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (a * x) : ℂ) * ψ x) :
    ψ = fun x => (Real.exp (-(a * x)) : ℂ) * g x := funext (psi_eq hg)

lemma continuous_psi {a : ℝ} {ψ : ℝ → ℂ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (a * x) : ℂ) * ψ x) : Continuous ψ := by
  rw [psi_funext hg]
  exact Continuous.mul (by fun_prop) g.continuous

lemma norm_cexp_mul (s : ℂ) (x : ℝ) : ‖Complex.exp (s * x)‖ = Real.exp (s.re * x) := by
  rw [Complex.norm_exp]; congr 1; simp

lemma norm_integrand {σ : ℝ} {ψ : ℝ → ℂ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (σ * x) : ℂ) * ψ x) {s : ℂ} (hs : s.re = σ) (x : ℝ) :
    ‖ψ x * Complex.exp (s * x)‖ = ‖g x‖ := by
  rw [norm_mul, norm_cexp_mul, hg, norm_mul, hs, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]

lemma integrable_of {σ : ℝ} {ψ : ℝ → ℂ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (σ * x) : ℂ) * ψ x) {s : ℂ} (hs : s.re = σ) :
    Integrable (fun x : ℝ => ψ x * Complex.exp (s * x)) := by
  refine Integrable.mono' g.integrable.norm ?_
    (Filter.Eventually.of_forall fun x => le_of_eq (norm_integrand hg hs x))
  exact ((continuous_psi hg).mul (by fun_prop)).aestronglyMeasurable

lemma exp_le_add (a b σ x : ℝ) (h1 : a ≤ σ) (h2 : σ ≤ b) :
    Real.exp (σ * x) ≤ Real.exp (a * x) + Real.exp (b * x) := by
  rcases le_total 0 x with hx | hx
  · have : Real.exp (σ * x) ≤ Real.exp (b * x) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h2 hx)
    linarith [Real.exp_pos (a * x)]
  · have : Real.exp (σ * x) ≤ Real.exp (a * x) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right h1 hx)
    linarith [Real.exp_pos (b * x)]

lemma norm_le_sum {a b σ : ℝ} {ψ : ℝ → ℂ} {ga gb : SchwartzMap ℝ ℂ}
    (ha : ∀ x, ga x = (Real.exp (a * x) : ℂ) * ψ x) (hb : ∀ x, gb x = (Real.exp (b * x) : ℂ) * ψ x)
    (h1 : a ≤ σ) (h2 : σ ≤ b) (x : ℝ) :
    ‖ψ x‖ * Real.exp (σ * x) ≤ ‖ga x‖ + ‖gb x‖ := by
  rw [ha, hb, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  have := exp_le_add a b σ x h1 h2
  nlinarith [norm_nonneg (ψ x)]

lemma hasDerivAt_psi {a : ℝ} {ψ : ℝ → ℂ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (a * x) : ℂ) * ψ x) (x : ℝ) :
    HasDerivAt ψ (((Real.exp (-(a * x)) * -(a * 1) : ℝ) : ℂ) * g x +
      (Real.exp (-(a * x)) : ℂ) * deriv g x) x := by
  rw [psi_funext hg]
  have h1 : HasDerivAt (fun x : ℝ => (Real.exp (-(a * x)) : ℂ))
      ((Real.exp (-(a * x)) * -(a * 1) : ℝ) : ℂ) x :=
    (((hasDerivAt_id x).const_mul a).neg.exp).ofReal_comp
  exact h1.mul (g.hasDerivAt x)

lemma P_deriv {I : Set ℝ} {ψ : ℝ → ℂ} (hP : P I ψ) : P I (deriv ψ) := by
  intro a ha
  obtain ⟨g, hg⟩ := hP a ha
  refine ⟨SchwartzMap.derivCLM ℂ ℂ g - (a : ℂ) • g, fun x => ?_⟩
  rw [(hasDerivAt_psi hg x).deriv]
  simp only [SchwartzMap.sub_apply, SchwartzMap.derivCLM_apply, SchwartzMap.smul_apply,
    smul_eq_mul]
  have he : (Real.exp (a * x) : ℂ) * (Real.exp (-(a * x)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  push_cast
  push_cast at he
  linear_combination (-(deriv g x - (a : ℂ) * g x)) * he

lemma differentiable_of_P {I : Set ℝ} {ψ : ℝ → ℂ} (hP : P I ψ) (hne : I.Nonempty) :
    Differentiable ℝ ψ := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨g, hg⟩ := hP a ha
  exact fun x => (hasDerivAt_psi hg x).differentiableAt

lemma ibp {I : Set ℝ} {ψ : ℝ → ℂ} (hP : P I ψ) {s : ℂ} (hs : s.re ∈ I) :
    s * ∫ x : ℝ, ψ x * Complex.exp (s * x) = -∫ x : ℝ, deriv ψ x * Complex.exp (s * x) := by
  obtain ⟨g, hg⟩ := hP _ hs
  obtain ⟨g', hg'⟩ := P_deriv hP _ hs
  have hd := differentiable_of_P hP ⟨_, hs⟩
  have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.exp (s * x)) (s * Complex.exp (s * x)) x := by
    intro x
    have h0 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (hasDerivAt_id' x).ofReal_comp
    have := (h0.const_mul s).cexp
    convert this using 1
    ring
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := ψ) (u' := deriv ψ)
    (v := fun x : ℝ => Complex.exp (s * x)) (v' := fun x : ℝ => s * Complex.exp (s * x))
    (fun x _ => (hd x).hasDerivAt) (fun x _ => hv x)
    (by
      have := (integrable_of hg rfl).const_mul s
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (integrable_of hg' rfl) (integrable_of hg rfl)
  rw [← key, ← integral_const_mul]
  congr 1
  funext x
  ring

lemma P_add {I : Set ℝ} {ψ φ : ℝ → ℂ} (h1 : P I ψ) (h2 : P I φ) : P I (ψ + φ) := by
  intro a ha
  obtain ⟨g1, hg1⟩ := h1 a ha
  obtain ⟨g2, hg2⟩ := h2 a ha
  exact ⟨g1 + g2, fun x => by simp only [SchwartzMap.add_apply, hg1, hg2, Pi.add_apply, mul_add]⟩

lemma P_smul {I : Set ℝ} {ψ : ℝ → ℂ} (c : ℂ) (h : P I ψ) : P I (c • ψ) := by
  intro a ha
  obtain ⟨g, hg⟩ := h a ha
  exact ⟨c • g, fun x => by
    simp only [SchwartzMap.smul_apply, hg, Pi.smul_apply, smul_eq_mul]; ring⟩

noncomputable def seq (a : ℝ) (ψ : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => ψ
  | m + 1 => deriv (seq a ψ m) + (a : ℂ) • seq a ψ m

lemma seq_P {I : Set ℝ} {ψ : ℝ → ℂ} (hP : P I ψ) (a : ℝ) (m : ℕ) : P I (seq a ψ m) := by
  induction m with
  | zero => exact hP
  | succ m ih => exact P_add (P_deriv ih) (P_smul _ ih)

lemma iteratedDeriv_seq {I : Set ℝ} {ψ : ℝ → ℂ} (hP : P I ψ) {a : ℝ} (ha : a ∈ I)
    {g : SchwartzMap ℝ ℂ} (hg : ∀ x, g x = (Real.exp (a * x) : ℂ) * ψ x) (m : ℕ) :
    ∀ x, iteratedDeriv m g x = (Real.exp (a * x) : ℂ) * seq a ψ m x := by
  induction m with
  | zero => intro x; rw [iteratedDeriv_zero]; exact hg x
  | succ m ih =>
    intro x
    rw [iteratedDeriv_succ, show iteratedDeriv m (⇑g) =
      fun x => (Real.exp (a * x) : ℂ) * seq a ψ m x from funext ih]
    have hd := differentiable_of_P (seq_P hP a m) ⟨a, ha⟩
    have h1 : HasDerivAt (fun x : ℝ => (Real.exp (a * x) : ℂ))
        ((Real.exp (a * x) * (a * 1) : ℝ) : ℂ) x :=
      (((hasDerivAt_id x).const_mul a).exp).ofReal_comp
    have hd2 : HasDerivAt (fun x : ℝ => (Real.exp (a * x) : ℂ) * seq a ψ m x)
        (((Real.exp (a * x) * (a * 1) : ℝ) : ℂ) * seq a ψ m x +
          (Real.exp (a * x) : ℂ) * deriv (seq a ψ m) x) x := h1.mul (hd x).hasDerivAt
    rw [hd2.deriv]
    simp only [seq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

lemma mellin_seq {I : Set ℝ} {ψ : ℝ → ℂ} (hP : P I ψ) (a : ℝ) {s : ℂ} (hs : s.re ∈ I) (m : ℕ) :
    ∫ x : ℝ, seq a ψ m x * Complex.exp (s * x) =
      ((a : ℂ) - s) ^ m * ∫ x : ℝ, ψ x * Complex.exp (s * x) := by
  induction m with
  | zero => simp [seq]
  | succ m ih =>
    have hPm := seq_P hP a m
    obtain ⟨g1, hg1⟩ := P_deriv hPm _ hs
    obtain ⟨g2, hg2⟩ := hPm _ hs
    have e1 := ibp hPm hs
    have e2 : ∫ x : ℝ, deriv (seq a ψ m) x * Complex.exp (s * x) =
        -(s * ∫ x : ℝ, seq a ψ m x * Complex.exp (s * x)) := by rw [e1, neg_neg]
    simp only [seq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
    rw [integral_add (integrable_of hg1 rfl) ((integrable_of hg2 rfl).const_mul (a : ℂ)),
      integral_const_mul, e2, ih]
    ring

noncomputable def ell (φ : ℝ → ℂ) (b : ℝ) (m : ℕ) : ℝ → ℂ := fun y =>
  ((b : ℂ) + y * Complex.I) ^ m * ∫ x : ℝ, φ x * Complex.exp (((b : ℂ) + y * Complex.I) * x)

lemma lineSchwartz (b : ℝ) (m : ℕ) (g : SchwartzMap ℝ ℂ) : ∃ G : SchwartzMap ℝ ℂ, ∀ y : ℝ,
    G y = ((b : ℂ) + y * Complex.I) ^ m * ∫ x : ℝ, g x * Complex.exp (y * Complex.I * x) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  let A : ℝ →L[ℝ] ℝ := (-(2 * Real.pi)⁻¹) • ContinuousLinearMap.id ℝ ℝ
  have hA : ∀ x, A x = -(2 * Real.pi)⁻¹ * x := fun x => by simp [A]
  have hg : (A : ℝ → ℝ).HasTemperateGrowth := A.hasTemperateGrowth
  have hup : ∃ (k : ℕ) (C : ℝ), ∀ x : ℝ, ‖x‖ ≤ C * (1 + ‖A x‖) ^ k := by
    refine ⟨1, 2 * Real.pi, fun x => ?_⟩
    rw [hA, pow_one, norm_mul, norm_neg, norm_inv, Real.norm_of_nonneg hpi.le, mul_add, mul_one,
      ← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul]
    linarith [norm_nonneg x, hpi]
  have hofR : (fun y : ℝ => (y : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth
  have hp : (fun y : ℝ => ((b : ℂ) + y * Complex.I) ^ m).HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const (b : ℂ)).add
      (hofR.mul (Function.HasTemperateGrowth.const Complex.I))).pow m
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => ((b : ℂ) + y * Complex.I) ^ m)
    (SchwartzMap.compCLM ℂ hg hup (SchwartzMap.fourierTransformCLM ℂ g)), fun y => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply hp, SchwartzMap.compCLM_apply, smul_eq_mul,
    Function.comp_apply, SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm, hA]
  congr 2
  push_cast
  field_simp

lemma integrand_eq (a y x : ℝ) (c : ℂ) :
    ((Real.exp (a * x) : ℂ) * c) * Complex.exp (y * Complex.I * x) =
      c * Complex.exp (((a : ℂ) + y * Complex.I) * x) := by
  rw [Complex.ofReal_exp,
    show ((a : ℂ) + y * Complex.I) * x = ((a * x : ℝ) : ℂ) + y * Complex.I * x by push_cast; ring,
    Complex.exp_add]
  ring

lemma ell_schwartz {φ : ℝ → ℂ} {b : ℝ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (b * x) : ℂ) * φ x) (m : ℕ) :
    ∃ G : SchwartzMap ℝ ℂ, ell φ b m = ⇑G := by
  obtain ⟨G, hG⟩ := lineSchwartz b m g
  refine ⟨G, funext fun y => ?_⟩
  rw [hG]
  unfold ell
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [hg, integrand_eq]

lemma norm_ell_succ (φ : ℝ → ℂ) (b : ℝ) (m : ℕ) (y : ℝ) :
    ‖ell φ b (m + 1) y‖ = ‖(b : ℂ) + y * Complex.I‖ * ‖ell φ b m y‖ := by
  unfold ell
  rw [pow_succ, norm_mul, norm_mul, norm_mul]
  ring

lemma cs_bound {I : Set ℝ} {φ : ℝ → ℂ} (hP : P I φ) {b : ℝ} (hb : b ∈ I) (m : ℕ) :
    ∫ y, ‖ell φ b m y‖ ≤ Real.sqrt Real.pi *
      ((eLpNorm (ell φ b m) 2 volume).toReal + (eLpNorm (ell φ b (m + 1)) 2 volume).toReal) := by
  obtain ⟨g, hg⟩ := hP b hb
  obtain ⟨G0, hG0⟩ := ell_schwartz hg m
  obtain ⟨G1, hG1⟩ := ell_schwartz hg (m + 1)
  have hpos : ∀ y : ℝ, 0 < 1 + y ^ 2 := fun y => by positivity
  have hfc : Continuous (fun y : ℝ => Real.sqrt ((1 + y ^ 2)⁻¹)) :=
    Real.continuous_sqrt.comp ((continuous_const.add (continuous_pow 2)).inv₀
      (fun y => (hpos y).ne'))
  have hhc : Continuous (fun y : ℝ => Real.sqrt (1 + y ^ 2) * ‖ell φ b m y‖) := by
    rw [hG0]
    exact (Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2))).mul
      G0.continuous.norm
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hfm : MemLp (fun y : ℝ => Real.sqrt ((1 + y ^ 2)⁻¹)) (ENNReal.ofReal 2) volume := by
    rw [h2, memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable]
    refine integrable_inv_one_add_sq.congr (Filter.Eventually.of_forall fun y => ?_)
    show (1 + y ^ 2)⁻¹ = ‖Real.sqrt ((1 + y ^ 2)⁻¹)‖ ^ 2
    rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (inv_nonneg.2 (hpos y).le)]
  have hbd : ∀ y : ℝ, Real.sqrt (1 + y ^ 2) * ‖ell φ b m y‖ ≤ ‖G0 y‖ + ‖G1 y‖ := by
    intro y
    have hs : Real.sqrt (1 + y ^ 2) ≤ 1 + ‖(b : ℂ) + y * Complex.I‖ := by
      have hy : |y| ≤ ‖(b : ℂ) + y * Complex.I‖ := by
        have := Complex.abs_im_le_norm ((b : ℂ) + y * Complex.I)
        simpa using this
      calc Real.sqrt (1 + y ^ 2) ≤ Real.sqrt ((1 + |y|) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [abs_nonneg y, sq_abs y])
        _ = 1 + |y| := Real.sqrt_sq (by positivity)
        _ ≤ 1 + ‖(b : ℂ) + y * Complex.I‖ := by linarith
    rw [← congrFun hG0 y, ← congrFun hG1 y, norm_ell_succ]
    have := norm_nonneg (ell φ b m y)
    nlinarith
  have hGm : MemLp (fun y : ℝ => ‖G0 y‖ + ‖G1 y‖) 2 volume :=
    ((G0.memLp 2 volume).norm).add ((G1.memLp 2 volume).norm)
  have hhm2 : MemLp (fun y : ℝ => Real.sqrt (1 + y ^ 2) * ‖ell φ b m y‖) 2 volume := by
    refine hGm.of_le hhc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact hbd y
  have hhm : MemLp (fun y : ℝ => Real.sqrt (1 + y ^ 2) * ‖ell φ b m y‖) (ENNReal.ofReal 2)
      volume := by rw [h2]; exact hhm2
  have H := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hfm hhm
  have hL : ∫ y, ‖Real.sqrt ((1 + y ^ 2)⁻¹)‖ * ‖Real.sqrt (1 + y ^ 2) * ‖ell φ b m y‖‖ =
      ∫ y, ‖ell φ b m y‖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (by positivity),
      Real.sqrt_inv, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.2 (hpos y)).ne', one_mul]
  have hF : ∫ y, ‖Real.sqrt ((1 + y ^ 2)⁻¹)‖ ^ (2 : ℝ) = Real.pi := by
    rw [← integral_univ_inv_one_add_sq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (inv_nonneg.2 (hpos y).le)]
  have hE := hhm2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have hEr : (∫ y, ‖Real.sqrt (1 + y ^ 2) * ‖ell φ b m y‖‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      (eLpNorm (fun y : ℝ => Real.sqrt (1 + y ^ 2) * ‖ell φ b m y‖) 2 volume).toReal := by
    rw [hE, ENNReal.toReal_ofReal (by positivity)]
    norm_num
  rw [hL, hF, hEr, ← Real.sqrt_eq_rpow] at H
  have hle : eLpNorm (fun y : ℝ => Real.sqrt (1 + y ^ 2) * ‖ell φ b m y‖) 2 volume ≤
      eLpNorm (ell φ b m) 2 volume + eLpNorm (ell φ b (m + 1)) 2 volume := by
    calc _ ≤ eLpNorm (fun y : ℝ => ‖G0 y‖ + ‖G1 y‖) 2 volume := by
          refine eLpNorm_mono fun y => ?_
          rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
          exact hbd y
      _ ≤ eLpNorm (fun y : ℝ => ‖G0 y‖) 2 volume + eLpNorm (fun y : ℝ => ‖G1 y‖) 2 volume :=
          eLpNorm_add_le G0.continuous.norm.aestronglyMeasurable
            G1.continuous.norm.aestronglyMeasurable (by norm_num)
      _ = _ := by rw [eLpNorm_norm, eLpNorm_norm, hG0, hG1]
  have hfin : eLpNorm (ell φ b m) 2 volume + eLpNorm (ell φ b (m + 1)) 2 volume ≠ ⊤ := by
    rw [hG0, hG1]
    exact ENNReal.add_ne_top.2 ⟨(G0.memLp 2 volume).eLpNorm_ne_top,
      (G1.memLp 2 volume).eLpNorm_ne_top⟩
  have hle' := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.1 hfin).1 (ENNReal.add_ne_top.1 hfin).2] at hle'
  calc ∫ y, ‖ell φ b m y‖ ≤ Real.sqrt Real.pi *
        (eLpNorm (fun y : ℝ => Real.sqrt (1 + y ^ 2) * ‖ell φ b m y‖) 2 volume).toReal := H
    _ ≤ _ := mul_le_mul_of_nonneg_left hle' (Real.sqrt_nonneg _)

lemma inv_bound {I : Set ℝ} {φ : ℝ → ℂ} (hP : P I φ) {b : ℝ} (hb : b ∈ I) (x : ℝ) :
    Real.exp (b * x) * ‖φ x‖ ≤ (2 * Real.pi)⁻¹ * ∫ y, ‖ell φ b 0 y‖ := by
  obtain ⟨h, hh⟩ := hP b hb
  have e1 : Real.exp (b * x) * ‖φ x‖ = ‖h x‖ := by
    rw [hh, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [e1]
  have hinv : h x = 𝓕⁻ (𝓕 (h : ℝ → ℂ)) x := by
    have h0 : (𝓕⁻ ((𝓕 h : SchwartzMap ℝ ℂ)) : SchwartzMap ℝ ℂ) = h := fourierInv_fourier_eq h
    have := congrArg (fun F : SchwartzMap ℝ ℂ => F x) h0
    rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] at this
    exact this.symm
  have hpt : ∀ v : ℝ, 𝓕 (h : ℝ → ℂ) v = ell φ b 0 ((-(2 * Real.pi)) * v) := by
    intro v
    rw [Real.fourier_real_eq_integral_exp_smul]
    unfold ell
    rw [pow_zero, one_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    have hx : Complex.exp (((b : ℂ) + ((-(2 * Real.pi) * v : ℝ) : ℂ) * Complex.I) * x) =
        Complex.exp ((b * x : ℝ) : ℂ) *
          Complex.exp (((-2 * Real.pi * x * v : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [smul_eq_mul, hh, Complex.ofReal_exp, hx]
    ring
  calc ‖h x‖ = ‖𝓕⁻ (𝓕 (h : ℝ → ℂ)) x‖ := by rw [← hinv]
    _ ≤ ∫ v, ‖𝓕 (h : ℝ → ℂ) v‖ := by
        rw [Real.fourierInv_eq]
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        simp_rw [Circle.norm_smul]
    _ = ∫ v, ‖ell φ b 0 ((-(2 * Real.pi)) * v)‖ := by simp_rw [hpt]
    _ = (2 * Real.pi)⁻¹ * ∫ y, ‖ell φ b 0 y‖ := by
        rw [Measure.integral_comp_mul_left (fun y => ‖ell φ b 0 y‖) (-(2 * Real.pi)),
          smul_eq_mul, inv_neg, abs_neg, abs_of_pos (by positivity)]

lemma add_pow_le_two (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ) :
    (u + v) ^ n ≤ 2 ^ n * (u ^ n + v ^ n) := by
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  rcases le_total u v with h | h
  · calc (u + v) ^ n ≤ (2 * v) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * v ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (u ^ n + v ^ n) := by have := pow_nonneg hu n; nlinarith
  · calc (u + v) ^ n ≤ (2 * u) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * u ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (u ^ n + v ^ n) := by have := pow_nonneg hv n; nlinarith

lemma weight (a δ x : ℝ) (hδ : 0 < δ) (k : ℕ) :
    |x| ^ k * Real.exp (a * x) ≤
      (k.factorial / δ ^ k) * (Real.exp ((a - δ) * x) + Real.exp ((a + δ) * x)) := by
  have h1 := Real.pow_div_factorial_le_exp (δ * |x|) (mul_nonneg hδ.le (abs_nonneg x)) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hdk : (0 : ℝ) < δ ^ k := by positivity
  rw [mul_pow, div_le_iff₀ hf] at h1
  have h2 : |x| ^ k ≤ (k.factorial / δ ^ k) * Real.exp (δ * |x|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hdk]
    nlinarith [Real.exp_pos (δ * |x|)]
  have h3 : Real.exp (δ * |x|) * Real.exp (a * x) ≤
      Real.exp ((a - δ) * x) + Real.exp ((a + δ) * x) := by
    rw [← Real.exp_add]
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx, show δ * x + a * x = (a + δ) * x by ring]
      linarith [Real.exp_pos ((a - δ) * x)]
    · rw [abs_of_nonpos hx, show δ * -x + a * x = (a - δ) * x by ring]
      linarith [Real.exp_pos ((a + δ) * x)]
  calc |x| ^ k * Real.exp (a * x) ≤ (k.factorial / δ ^ k) * Real.exp (δ * |x|) *
        Real.exp (a * x) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (k.factorial / δ ^ k) * (Real.exp (δ * |x|) * Real.exp (a * x)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

lemma bound_b {I : Set ℝ} {ψ : ℝ → ℂ} (hP : P I ψ) (a : ℝ) (n : ℕ) {b : ℝ} (hb : b ∈ I)
    (x : ℝ) :
    Real.exp (b * x) * ‖seq a ψ n x‖ ≤ (2 * Real.pi)⁻¹ * 2 ^ n * Real.sqrt Real.pi *
      (|a| ^ n * ((eLpNorm (ell ψ b 0) 2 volume).toReal +
          (eLpNorm (ell ψ b 1) 2 volume).toReal) +
        ((eLpNorm (ell ψ b n) 2 volume).toReal + (eLpNorm (ell ψ b (n + 1)) 2 volume).toReal)) := by
  have hPn := seq_P hP a n
  have h1 := inv_bound hPn hb x
  obtain ⟨gb, hgb⟩ := hP b hb
  obtain ⟨gn, hgn⟩ := hPn b hb
  obtain ⟨G0, hG0⟩ := ell_schwartz hgb 0
  obtain ⟨Gn, hGn⟩ := ell_schwartz hgb n
  obtain ⟨H0, hH0⟩ := ell_schwartz hgn 0
  have hpt : ∀ y : ℝ, ‖ell (seq a ψ n) b 0 y‖ ≤
      2 ^ n * (|a| ^ n * ‖ell ψ b 0 y‖ + ‖ell ψ b n y‖) := by
    intro y
    have hs : ((b : ℂ) + y * Complex.I).re ∈ I := by simpa using hb
    have e : ell (seq a ψ n) b 0 y = ((a : ℂ) - ((b : ℂ) + y * Complex.I)) ^ n *
        ∫ x : ℝ, ψ x * Complex.exp (((b : ℂ) + y * Complex.I) * x) := by
      unfold ell
      rw [pow_zero, one_mul, mellin_seq hP a hs n]
    have e0 : ell ψ b 0 y = ∫ x : ℝ, ψ x * Complex.exp (((b : ℂ) + y * Complex.I) * x) := by
      unfold ell; rw [pow_zero, one_mul]
    have en : ‖ell ψ b n y‖ = ‖(b : ℂ) + y * Complex.I‖ ^ n * ‖ell ψ b 0 y‖ := by
      unfold ell; rw [norm_mul, norm_pow, pow_zero, one_mul]
    rw [e, norm_mul, norm_pow, en, ← e0]
    have ht : ‖(a : ℂ) - ((b : ℂ) + y * Complex.I)‖ ≤ |a| + ‖(b : ℂ) + y * Complex.I‖ := by
      have := norm_sub_le (a : ℂ) ((b : ℂ) + y * Complex.I)
      rwa [Complex.norm_real, Real.norm_eq_abs] at this
    have hp := (pow_le_pow_left₀ (norm_nonneg _) ht n).trans
      (add_pow_le_two |a| ‖(b : ℂ) + y * Complex.I‖ (abs_nonneg a) (norm_nonneg _) n)
    have := norm_nonneg (ell ψ b 0 y)
    calc ‖(a : ℂ) - ((b : ℂ) + y * Complex.I)‖ ^ n * ‖ell ψ b 0 y‖ ≤
        2 ^ n * (|a| ^ n + ‖(b : ℂ) + y * Complex.I‖ ^ n) * ‖ell ψ b 0 y‖ :=
          mul_le_mul_of_nonneg_right hp this
      _ = _ := by ring
  have hint : ∫ y, ‖ell (seq a ψ n) b 0 y‖ ≤
      2 ^ n * (|a| ^ n * (∫ y, ‖ell ψ b 0 y‖) + ∫ y, ‖ell ψ b n y‖) := by
    have i0 : Integrable (fun y => ‖ell ψ b 0 y‖) := by rw [hG0]; exact G0.integrable.norm
    have i1 : Integrable (fun y => ‖ell ψ b n y‖) := by rw [hGn]; exact Gn.integrable.norm
    have iH : Integrable (fun y => ‖ell (seq a ψ n) b 0 y‖) := by
      rw [hH0]; exact H0.integrable.norm
    calc ∫ y, ‖ell (seq a ψ n) b 0 y‖ ≤
        ∫ y, 2 ^ n * (|a| ^ n * ‖ell ψ b 0 y‖ + ‖ell ψ b n y‖) :=
          integral_mono iH (((i0.const_mul _).add i1).const_mul _) hpt
      _ = _ := by
          rw [integral_const_mul, integral_add (i0.const_mul _) i1, integral_const_mul]
  have c0 := cs_bound hP hb 0
  have cn := cs_bound hP hb n
  have hsq := Real.sqrt_nonneg Real.pi
  have hpi : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  have han : (0 : ℝ) ≤ |a| ^ n := by positivity
  calc Real.exp (b * x) * ‖seq a ψ n x‖ ≤ (2 * Real.pi)⁻¹ * ∫ y, ‖ell (seq a ψ n) b 0 y‖ := h1
    _ ≤ (2 * Real.pi)⁻¹ * (2 ^ n * (|a| ^ n * (∫ y, ‖ell ψ b 0 y‖) + ∫ y, ‖ell ψ b n y‖)) :=
        mul_le_mul_of_nonneg_left hint hpi
    _ ≤ (2 * Real.pi)⁻¹ * (2 ^ n * (|a| ^ n * (Real.sqrt Real.pi *
          ((eLpNorm (ell ψ b 0) 2 volume).toReal + (eLpNorm (ell ψ b (0 + 1)) 2 volume).toReal))
          + Real.sqrt Real.pi * ((eLpNorm (ell ψ b n) 2 volume).toReal +
            (eLpNorm (ell ψ b (n + 1)) 2 volume).toReal))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left c0 han) cn) h2n) hpi
    _ = _ := by ring

end B3Aux

open B3Aux in
theorem solution (I : Set ℝ) (hI : IsOpen I) (a : ℝ) (ha : a ∈ I) (k n : ℕ) :
    ∃ (S : Finset (ℝ × ℕ)) (C : ℝ), (∀ p ∈ S, p.1 ∈ I) ∧
      ∀ (ψ : ℝ → ℂ) (g : ℝ → SchwartzMap ℝ ℂ),
        (∀ b ∈ I, ∀ x : ℝ, g b x = (Real.exp (b * x) : ℂ) * ψ x) →
        SchwartzMap.seminorm ℂ k n (g a) ≤
          C * ∑ p ∈ S, (eLpNorm (fun y : ℝ => ((p.1 : ℂ) + y * Complex.I) ^ p.2 *
            ∫ x : ℝ, ψ x * Complex.exp (((p.1 : ℂ) + y * Complex.I) * x)) 2 volume).toReal := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI a ha
  have hδ : 0 < ε / 2 := by positivity
  have hlo : a - ε / 2 ∈ I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have hhi : a + ε / 2 ∈ I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have hne : a - ε / 2 ≠ a + ε / 2 := by intro h; linarith
  let B : Finset ℝ := {a - ε / 2, a + ε / 2}
  let J : Finset ℕ := Finset.range (n + 2)
  let K : ℝ := (2 * Real.pi)⁻¹ * 2 ^ n * Real.sqrt Real.pi
  let Cw : ℝ := k.factorial / (ε / 2) ^ k
  refine ⟨B ×ˢ J, Cw * (K * (|a| ^ n + 1)), ?_, fun ψ g hg => ?_⟩
  · intro p hp
    rw [Finset.mem_product] at hp
    rcases Finset.mem_insert.1 hp.1 with h | h
    · rw [h]; exact hlo
    · rw [Finset.mem_singleton.1 h]; exact hhi
  have hP : P I ψ := fun b hb => ⟨g b, hg b hb⟩
  let E : ℝ → ℕ → ℝ := fun b j => (eLpNorm (ell ψ b j) 2 volume).toReal
  have hE0 : ∀ b j, 0 ≤ E b j := fun _ _ => ENNReal.toReal_nonneg
  let R : ℝ → ℝ := fun b => ∑ j ∈ J, E b j
  have hsum : ∑ p ∈ B ×ˢ J, (eLpNorm (fun y : ℝ => ((p.1 : ℂ) + y * Complex.I) ^ p.2 *
      ∫ x : ℝ, ψ x * Complex.exp (((p.1 : ℂ) + y * Complex.I) * x)) 2 volume).toReal =
      R (a - ε / 2) + R (a + ε / 2) := by
    rw [Finset.sum_product, Finset.sum_pair hne]
    rfl
  have hR : ∀ b, E b 0 + E b 1 ≤ R b ∧ E b n + E b (n + 1) ≤ R b := by
    intro b
    constructor
    · have : ({0, 1} : Finset ℕ) ⊆ J := by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [J, Finset.mem_range]; omega
      have h := Finset.sum_le_sum_of_subset_of_nonneg this (fun j _ _ => hE0 b j)
      rwa [Finset.sum_pair (by norm_num)] at h
    · have : ({n, n + 1} : Finset ℕ) ⊆ J := by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [J, Finset.mem_range]; omega
      have h := Finset.sum_le_sum_of_subset_of_nonneg this (fun j _ _ => hE0 b j)
      rwa [Finset.sum_pair (by omega)] at h
  have hRb : ∀ b ∈ I, ∀ x : ℝ, Real.exp (b * x) * ‖seq a ψ n x‖ ≤ K * (|a| ^ n + 1) * R b := by
    intro b hb x
    have h := bound_b hP a n hb x
    obtain ⟨h1, h2⟩ := hR b
    have hK : 0 ≤ K := by positivity
    have han : (0 : ℝ) ≤ |a| ^ n := by positivity
    calc _ ≤ K * (|a| ^ n * (E b 0 + E b 1) + (E b n + E b (n + 1))) := h
      _ ≤ K * (|a| ^ n * R b + R b) := by gcongr
      _ = K * (|a| ^ n + 1) * R b := by ring
  have hRnn : ∀ b, 0 ≤ R b := fun b => Finset.sum_nonneg fun j _ => hE0 b j
  rw [hsum]
  have hCw : 0 ≤ Cw := by positivity
  have hK1 : 0 ≤ K * (|a| ^ n + 1) := by positivity
  refine SchwartzMap.seminorm_le_bound' ℂ k n (g a)
    (by have := hRnn (a - ε / 2); have := hRnn (a + ε / 2); positivity) (fun x => ?_)
  rw [iteratedDeriv_seq hP ha (hg a ha) n x, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have hw := weight a (ε / 2) x hδ k
  have h1 := hRb _ hlo x
  have h2 := hRb _ hhi x
  have hs := norm_nonneg (seq a ψ n x)
  calc |x| ^ k * (Real.exp (a * x) * ‖seq a ψ n x‖) =
      (|x| ^ k * Real.exp (a * x)) * ‖seq a ψ n x‖ := by ring
    _ ≤ Cw * (Real.exp ((a - ε / 2) * x) + Real.exp ((a + ε / 2) * x)) * ‖seq a ψ n x‖ :=
        mul_le_mul_of_nonneg_right hw hs
    _ = Cw * (Real.exp ((a - ε / 2) * x) * ‖seq a ψ n x‖ +
          Real.exp ((a + ε / 2) * x) * ‖seq a ψ n x‖) := by ring
    _ ≤ Cw * (K * (|a| ^ n + 1) * R (a - ε / 2) + K * (|a| ^ n + 1) * R (a + ε / 2)) := by
        gcongr
    _ = _ := by ring
