-- Prove2me | solution 1 for MasulloRH.regularized_spectral_domination_any_window
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-20T23:30:36.212442+00:00
-- url     : https://prove2.me/submissions/8a6ffe38-96e3-4e05-bd5d-4510cb40ceaa

/- Generalized from yikerman’s Prove2Me submission 42c63ae0-e742-45d0-93c9-bdffead20b87, licensed under Apache-2.0. The original Fourier estimates are unchanged. -/
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MasulloRH MeasureTheory Set Filter
open scoped Topology ContDiff
set_option autoImplicit false

private noncomputable def gate (x : ℝ) := Real.smoothTransition (x - 1)
private noncomputable def gateCut (p q x : ℝ) := gate (p*x) * (1 - gate (q*x))

private theorem gate_smooth : ContDiff ℝ ∞ gate :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

private theorem gateCut_smooth (p q : ℝ) : ContDiff ℝ ∞ (gateCut p q) :=
  (gate_smooth.comp (contDiff_const.mul contDiff_id)).mul
    (contDiff_const.sub (gate_smooth.comp (contDiff_const.mul contDiff_id)))

private theorem gateCut_unit (p q x : ℝ) : |gateCut p q x| ≤ 1 := by
  have h1 := Real.smoothTransition.nonneg (p*x-1)
  have h2 := Real.smoothTransition.le_one (q*x-1)
  rw [gateCut, gate, gate, abs_of_nonneg (mul_nonneg h1 (sub_nonneg.mpr h2))]
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (sub_nonneg.mpr h2)
    (sub_le_self _ (Real.smoothTransition.nonneg _))

private theorem gateCut_zero_left {p q x : ℝ} (hp : 0 < p) (hx : x < 1/p) :
    gateCut p q x = 0 := by
  have h := (lt_div_iff₀ hp).mp hx
  simp [gateCut, gate, Real.smoothTransition.zero_of_nonpos
    (show p*x-1 ≤ 0 by linarith [mul_comm p x])]

private theorem gateCut_compact {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    HasCompactSupport (gateCut p q) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := 2/q))
  intro x hx
  change gateCut p q x ≠ 0 at hx
  constructor
  · by_contra! hl
    exact hx (gateCut_zero_left hp (hl.trans (by positivity)))
  · by_contra! hi
    have h := (div_lt_iff₀ hq).mp hi
    exact hx (by simp [gateCut, gate, Real.smoothTransition.one_of_one_le
      (show 1 ≤ q*x-1 by linarith [mul_comm q x])])

private theorem gate_deriv_compact : HasCompactSupport (deriv gate) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 1) (b := 2))
  intro x hx
  change deriv gate x ≠ 0 at hx
  constructor
  · by_contra! h
    have he : gate =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [gt_mem_nhds h] with t ht
      exact Real.smoothTransition.zero_of_nonpos (by linarith)
    exact hx (he.deriv_eq.trans (by simp))
  · by_contra! h
    have he : gate =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [lt_mem_nhds h] with t ht
      exact Real.smoothTransition.one_of_one_le (by linarith)
    exact hx (he.deriv_eq.trans (by simp))

private theorem gate_chain (p x : ℝ) :
    HasDerivAt (fun t : ℝ => gate (p*t)) (deriv gate (p*x) * p) x :=
  ((gate_smooth.differentiable (by simp)).differentiableAt.hasDerivAt).comp x
    (hasDerivAt_const_mul p)

private theorem gate_deriv_chain (p x : ℝ) :
    HasDerivAt (fun t : ℝ => deriv gate (p*t)) (deriv (deriv gate) (p*x) * p) x :=
  (((contDiff_infty_iff_deriv.mp gate_smooth).2.differentiable (by simp)).differentiableAt.hasDerivAt).comp x
    (hasDerivAt_const_mul p)

private theorem gateCut_d1 (p q x : ℝ) :
    deriv (gateCut p q) x = (deriv gate (p*x)*p)*(1-gate (q*x)) -
      gate (p*x)*(deriv gate (q*x)*q) := by
  convert ((gate_chain p x).mul ((hasDerivAt_const x (1 : ℝ)).sub (gate_chain q x))).deriv using 1 <;> first | rfl | (simp only [Pi.sub_apply]; ring)

private theorem gateCut_d2 (p q x : ℝ) :
    deriv (deriv (gateCut p q)) x =
      (deriv (deriv gate) (p*x)*p^2)*(1-gate (q*x)) -
      2*(deriv gate (p*x)*p)*(deriv gate (q*x)*q) -
      gate (p*x)*(deriv (deriv gate) (q*x)*q^2) := by
  rw [show deriv (gateCut p q) = _ from funext (gateCut_d1 p q)]
  convert (((gate_deriv_chain p x).mul_const p).mul
    ((hasDerivAt_const x (1 : ℝ)).sub (gate_chain q x)) |>.sub
    ((gate_chain p x).mul ((gate_deriv_chain q x).mul_const q))).deriv using 1 <;> first | rfl | (simp only [Pi.sub_apply]; ring)

private noncomputable def dilateMass (p : ℝ) (f : ℝ → ℝ) (x : ℝ) := p * f (p*x)

private theorem dilateMass_integrable {p : ℝ} (hp : 0 < p) {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (dilateMass p f) := (hf.comp_mul_left' hp.ne').const_mul _

private theorem dilateMass_integral {p : ℝ} (hp : 0 < p) (f : ℝ → ℝ) :
    (∫ x, dilateMass p f x) = ∫ x, f x := by
  simp only [dilateMass, integral_const_mul, Measure.integral_comp_mul_left,
    abs_of_nonneg (inv_nonneg.mpr hp.le), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]

private theorem gate_abs (x : ℝ) : |gate x| ≤ 1 := by
  rw [gate, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

private theorem gate_compl_abs (x : ℝ) : |1-gate x| ≤ 1 := by
  rw [gate, abs_of_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one _))]
  exact sub_le_self _ (Real.smoothTransition.nonneg _)

private theorem abs_sub_bound (u v : ℝ) : |u-v| ≤ |u|+|v| := norm_sub_le u v

private theorem gateCut_d1_bound {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (x : ℝ) :
    |deriv (gateCut p q) x| ≤ dilateMass p (fun z => |deriv gate z|) x +
      dilateMass q (fun z => |deriv gate z|) x := by
  rw [gateCut_d1]
  refine (abs_sub_bound _ _).trans ?_
  simp only [abs_mul, abs_of_pos hp, abs_of_pos hq, dilateMass]
  calc
    _ ≤ |deriv gate (p*x)| * p * 1 + 1 * (|deriv gate (q*x)| * q) := by
      gcongr
      · exact gate_compl_abs _
      · exact gate_abs _
    _ = _ := by ring

-- The factor |x| absorbs the extra dilation in each second derivative.
private theorem gateCut_d2_bound {p q M : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hM : ∀ z : ℝ, |z| * |deriv gate z| ≤ M) (x : ℝ) :
    |x| * |deriv (deriv (gateCut p q)) x| ≤
      dilateMass p (fun z => |z| * |deriv (deriv gate) z|) x +
      (2*M) * dilateMass p (fun z => |deriv gate z|) x +
      dilateMass q (fun z => |z| * |deriv (deriv gate) z|) x := by
  rw [gateCut_d2]
  have htri (A B C : ℝ) : |A-B-C| ≤ |A|+|B|+|C| :=
    (abs_sub_bound _ _).trans (add_le_add (abs_sub_bound _ _) le_rfl)
  refine (mul_le_mul_of_nonneg_left (htri _ _ _) (abs_nonneg x)).trans ?_
  have hM' := hM (q*x)
  simp only [dilateMass, abs_mul, abs_pow, abs_of_pos hp, abs_of_pos hq,
    abs_of_pos (show 0 < (2 : ℝ) by norm_num)] at hM' ⊢
  calc
    _ ≤ |x| * (|deriv (deriv gate) (p*x)| * p^2 * 1 +
      2*(|deriv gate (p*x)| * p)*(|deriv gate (q*x)| * q) +
      1*(|deriv (deriv gate) (q*x)| * q^2)) := by
        gcongr
        · exact gate_compl_abs _
        · exact gate_abs _
    _ = p * (p * |x| * |deriv (deriv gate) (p*x)|) +
        (2*(q * |x| * |deriv gate (q*x)|)) * (p * |deriv gate (p*x)|) +
        q * (q * |x| * |deriv (deriv gate) (q*x)|) := by ring
    _ ≤ _ := by gcongr

private theorem gateCut_bounds : ∃ D : ℝ, 0 ≤ D ∧ ∀ (p q : ℝ), 0 < p → 0 < q →
    (∫ x, |deriv (gateCut p q) x|) ≤ D ∧
    (∫ x, |x| * |deriv (deriv (gateCut p q)) x|) ≤ D := by
  let u := fun x : ℝ => |deriv gate x|
  let v := fun x : ℝ => |x| * |deriv (deriv gate) x|
  have h1 := (contDiff_infty_iff_deriv.mp gate_smooth).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  have hu : Integrable u := (h1.continuous.integrable_of_hasCompactSupport gate_deriv_compact).norm
  have hv : Integrable v := by
    have hc : Continuous (fun x : ℝ => x * deriv (deriv gate) x) := continuous_id.mul h2.continuous
    have hs : HasCompactSupport (fun x : ℝ => x * deriv (deriv gate) x) :=
      gate_deriv_compact.deriv.mul_left (f := id)
    simpa only [v, Real.norm_eq_abs, abs_mul] using (hc.integrable_of_hasCompactSupport hs).norm
  have hc : HasCompactSupport (fun x : ℝ => x * deriv gate x) := gate_deriv_compact.mul_left (f := id)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous (continuous_id.mul h1.continuous)
  simp only [Real.norm_eq_abs, abs_mul] at hM
  let D1 := (∫ x, u x) + ∫ x, u x
  let D2 := (∫ x, v x) + (2*M)*(∫ x, u x) + ∫ x, v x
  refine ⟨max D1 D2, le_max_of_le_left ?_, fun p q hp hq => ⟨?_, ?_⟩⟩
  · have h : 0 ≤ ∫ x, u x := integral_nonneg (fun x => abs_nonneg _)
    exact add_nonneg h h
  · refine le_trans ?_ (le_max_left D1 D2)
    have hc := (gateCut_compact hp hq).deriv
    have hd := (contDiff_infty_iff_deriv.mp (gateCut_smooth p q)).2
    calc
      _ ≤ ∫ x, dilateMass p u x + dilateMass q u x := integral_mono
        (hd.continuous.integrable_of_hasCompactSupport hc).norm
        ((dilateMass_integrable hp hu).add (dilateMass_integrable hq hu)) (gateCut_d1_bound hp hq)
      _ = _ := by rw [integral_add (dilateMass_integrable hp hu) (dilateMass_integrable hq hu),
                    dilateMass_integral hp, dilateMass_integral hq]
  · refine le_trans ?_ (le_max_right D1 D2)
    have hc : HasCompactSupport (fun x : ℝ => x * deriv (deriv (gateCut p q)) x) :=
      (gateCut_compact hp hq).deriv.deriv.mul_left (f := id)
    have hd := (contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp (gateCut_smooth p q)).2)).2
    have hint := ((continuous_id.mul hd.continuous).integrable_of_hasCompactSupport (μ := volume) hc).norm
    simp only [Pi.mul_apply, id_eq, Real.norm_eq_abs, abs_mul] at hint
    have hu' := (dilateMass_integrable hp hu).const_mul (2*M)
    have huv : Integrable (fun x => dilateMass p v x + (2*M)*dilateMass p u x) :=
      (dilateMass_integrable hp hv).add hu'
    calc
      _ ≤ ∫ x, dilateMass p v x + (2*M)*dilateMass p u x + dilateMass q v x :=
        integral_mono hint (((dilateMass_integrable hp hv).add hu').add (dilateMass_integrable hq hv))
          (gateCut_d2_bound hp hq hM)
      _ = _ := by rw [integral_add huv (dilateMass_integrable hq hv),
                    integral_add (dilateMass_integrable hp hv) hu', integral_const_mul,
                    dilateMass_integral hp, dilateMass_integral hp, dilateMass_integral hq]

private noncomputable def expDiff (a b : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (a * x) - Complex.exp (b * x)

private theorem expDiff_smooth (a b : ℂ) : ContDiff ℝ ∞ (expDiff a b) := by
  have hor : ContDiff ℝ ∞ ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  unfold expDiff
  fun_prop (disch := assumption)

private theorem decayExp_hasDeriv (a : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (a * y)) (a * Complex.exp (a * x)) x := by
  simpa [mul_comm] using
    ((Complex.hasDerivAt_exp (a * (x : ℂ))).comp (x : ℂ) (hasDerivAt_const_mul a)).comp_ofReal

private theorem expDiff_d1 (a b : ℂ) (x : ℝ) :
    deriv (expDiff a b) x = a * Complex.exp (a * x) - b * Complex.exp (b * x) :=
  ((decayExp_hasDeriv a x).sub (decayExp_hasDeriv b x)).deriv

private theorem expDiff_d2 (a b : ℂ) (x : ℝ) :
    deriv (deriv (expDiff a b)) x =
      a ^ 2 * Complex.exp (a * x) - b ^ 2 * Complex.exp (b * x) := by
  rw [show deriv (expDiff a b) = _ from funext (expDiff_d1 a b)]
  calc _ = a * (a * Complex.exp (a * x)) - b * (b * Complex.exp (b * x)) :=
          (((decayExp_hasDeriv a x).const_mul a).sub ((decayExp_hasDeriv b x).const_mul b)).deriv
       _ = _ := by ring

private theorem decayExp_norm {a : ℂ} (ha : a.re ≤ -(1/2 : ℝ)) {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.exp (a * x)‖ ≤ Real.exp (-x / 2) := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_right ha hx])

private theorem expDiff_bounds (s : ℂ) (hs : (3/2 : ℝ) < s.re) :
    ∃ K : ℝ, 0 < K ∧ ∀ (r : ℝ), 0 < r → r < 1 → ∀ x : ℝ, 0 ≤ x →
      ‖expDiff ((r : ℂ) - s) ((r : ℂ) - 5 / 2) x‖ ≤ 2 * Real.exp (-x / 2) ∧
      ‖expDiff ((r : ℂ) - s) ((r : ℂ) - 5 / 2) x‖ ≤ K * |x| ∧
      ‖deriv (expDiff ((r : ℂ) - s) ((r : ℂ) - 5 / 2)) x‖ ≤ K ∧
      ‖deriv (deriv (expDiff ((r : ℂ) - s) ((r : ℂ) - 5 / 2))) x‖ ≤ K * Real.exp (-x / 2) := by
  let L := ‖s‖ + 4
  let K := 2 * L ^ 2
  have hL : 1 ≤ L := by dsimp [L]; linarith [norm_nonneg s]
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro r hr hr'
  let a : ℂ := r - s
  let b : ℂ := r - 5 / 2
  have ha : a.re ≤ -(1/2 : ℝ) := by simp [a]; linarith
  have hb : b.re ≤ -(1/2 : ℝ) := by norm_num [b]; linarith
  have hna : ‖a‖ ≤ L := by
    have h := norm_sub_le (r : ℂ) s
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
    dsimp [a, L]
    linarith
  have hnb : ‖b‖ ≤ L := by
    have h := norm_sub_le (r : ℂ) (5 / 2 : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
    norm_num [norm_div] at h
    dsimp [b, L]
    linarith [norm_nonneg s]
  have hsum : ‖a‖ + ‖b‖ ≤ K := by dsimp [K]; nlinarith [sq_nonneg (L-1)]
  have hsq : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ K := by
    dsimp [K]
    nlinarith [sq_le_sq' (by linarith [norm_nonneg a] : -L ≤ ‖a‖) hna,
      sq_le_sq' (by linarith [norm_nonneg b] : -L ≤ ‖b‖) hnb]
  have hd1 (y : ℝ) (hy : 0 ≤ y) : ‖deriv (expDiff a b) y‖ ≤ K := by
    have hey : Real.exp (-y/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [expDiff_d1]
    calc _ ≤ ‖a * Complex.exp (a * y)‖ + ‖b * Complex.exp (b * y)‖ := norm_sub_le _ _
         _ ≤ ‖a‖ * 1 + ‖b‖ * 1 := by
           simp only [norm_mul]
           exact add_le_add (mul_le_mul_of_nonneg_left ((decayExp_norm ha hy).trans hey) (norm_nonneg _))
             (mul_le_mul_of_nonneg_left ((decayExp_norm hb hy).trans hey) (norm_nonneg _))
         _ ≤ K := by simpa using hsum
  intro x hx
  refine ⟨(norm_sub_le _ _).trans (by linarith [decayExp_norm ha hx, decayExp_norm hb hx]), ?_, hd1 x hx, ?_⟩
  · have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := (0 : ℝ)) (b := x) (f := expDiff a b) (f' := deriv (expDiff a b))
      (fun y _ => ((expDiff_smooth a b).differentiable (by simp)).differentiableAt.hasDerivAt.hasDerivWithinAt)
      (fun y hy => hd1 y hy.1) x ⟨hx, le_rfl⟩
    simpa [expDiff, abs_of_nonneg hx, a, b] using hmv
  · rw [expDiff_d2]
    calc _ ≤ ‖a ^ 2 * Complex.exp (a * x)‖ + ‖b ^ 2 * Complex.exp (b * x)‖ := norm_sub_le _ _
         _ ≤ ‖a‖ ^ 2 * Real.exp (-x / 2) + ‖b‖ ^ 2 * Real.exp (-x / 2) := by
           simp only [norm_mul, norm_pow]
           exact add_le_add (mul_le_mul_of_nonneg_left (decayExp_norm ha hx) (sq_nonneg _))
             (mul_le_mul_of_nonneg_left (decayExp_norm hb hx) (sq_nonneg _))
         _ ≤ K * Real.exp (-x / 2) := by rw [← add_mul]; exact mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le

private noncomputable def windowSignal (p q : ℝ) (a b : ℂ) (x : ℝ) : ℂ :=
  (gateCut p q x : ℂ) * expDiff a b x

private theorem windowSignal_smooth (p q : ℝ) (a b : ℂ) :
    ContDiff ℝ ∞ (windowSignal p q a b) :=
  (Complex.ofRealCLM.contDiff.comp (gateCut_smooth p q)).mul (expDiff_smooth a b)

private theorem windowSignal_compact {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (a b : ℂ) :
    HasCompactSupport (windowSignal p q a b) :=
  ((gateCut_compact hp hq).comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero).mul_right

private theorem windowSignal_d2_bound (p q : ℝ) (a b : ℂ) (K x : ℝ)
    (hn : ‖expDiff a b x‖ ≤ K * |x|)
    (h1 : ‖deriv (expDiff a b) x‖ ≤ K)
    (h2 : ‖deriv (deriv (expDiff a b)) x‖ ≤ K * Real.exp (-x / 2)) :
    ‖deriv (deriv (windowSignal p q a b)) x‖ ≤
      K * (|x| * |deriv (deriv (gateCut p q)) x|) +
        (2 * K) * |deriv (gateCut p q) x| + K * Real.exp (-x / 2) := by
  let c := gateCut p q
  let f := expDiff a b
  have dc (t : ℝ) : HasDerivAt c (deriv c t) t :=
    ((gateCut_smooth p q).differentiable (by simp)).differentiableAt.hasDerivAt
  have df (t : ℝ) : HasDerivAt f (deriv f t) t :=
    ((expDiff_smooth a b).differentiable (by simp)).differentiableAt.hasDerivAt
  have ddc : HasDerivAt (deriv c) (deriv (deriv c) x) x :=
    (((contDiff_infty_iff_deriv.mp (gateCut_smooth p q)).2.differentiable (by simp))).differentiableAt.hasDerivAt
  have ddf : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    (((contDiff_infty_iff_deriv.mp (expDiff_smooth a b)).2.differentiable (by simp))).differentiableAt.hasDerivAt
  have hfirst : deriv (windowSignal p q a b) =
      fun y => ((deriv c y : ℝ) : ℂ) * f y + (c y : ℂ) * deriv f y :=
    funext fun y => ((dc y).ofReal_comp.mul (df y)).deriv
  have hsecond := ((ddc.ofReal_comp.mul (df x)).add ((dc x).ofReal_comp.mul ddf)).deriv
  simp only [Pi.mul_def, Pi.add_def] at hsecond
  rw [hfirst, hsecond]
  calc _ ≤ (‖((deriv (deriv c) x : ℝ) : ℂ) * f x‖ + ‖((deriv c x : ℝ) : ℂ) * deriv f x‖) +
           (‖((deriv c x : ℝ) : ℂ) * deriv f x‖ + ‖(c x : ℂ) * deriv (deriv f) x‖) :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
       _ ≤ (|deriv (deriv c) x| * (K * |x|) + |deriv c x| * K) +
           (|deriv c x| * K + 1 * (K * Real.exp (-x / 2))) := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add
            (add_le_add (mul_le_mul_of_nonneg_left hn (abs_nonneg _))
              (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)))
            (add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
              (mul_le_mul (gateCut_unit p q x) h2 (norm_nonneg _) zero_le_one))
       _ = _ := by change _ = K * (|x| * |deriv (deriv c) x|) + (2*K) * |deriv c x| + _; ring

-- The difference of exponentials vanishes at zero. Its linear bound pairs with the
-- weighted second derivative of the cutoff, uniformly in both dilation parameters.
private theorem windowSignal_bounds (s : ℂ) (hs : (3/2 : ℝ) < s.re) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ Ioo (0 : ℝ) 1, ∀ (p q : ℝ), 0 < p → 0 < q →
      (∫ x, ‖windowSignal p q ((r : ℂ)-s) ((r : ℂ)-5/2) x‖) ≤ B ∧
      (∫ x, ‖deriv (deriv (windowSignal p q ((r : ℂ)-s) ((r : ℂ)-5/2))) x‖) ≤ B := by
  obtain ⟨D, hD, hd⟩ := gateCut_bounds
  obtain ⟨K, hK, hk⟩ := expDiff_bounds s hs
  let T := (Ioi (0 : ℝ)).indicator (fun x : ℝ => Real.exp ((-1 / 2) * x))
  have hT : Integrable T :=
    (integrableOn_exp_mul_Ioi (a := -1/2) (by norm_num) 0).integrable_indicator measurableSet_Ioi
  have hTval : (∫ x, T x) = 2 := by
    unfold T
    rw [integral_indicator measurableSet_Ioi, integral_exp_mul_Ioi (by norm_num)]
    norm_num
  have hTpos {x : ℝ} (hx : 0 < x) : T x = Real.exp (-x/2) := by
    simp only [T, indicator_of_mem (show x ∈ Ioi 0 from hx)]
    congr 1
    ring
  refine ⟨5 + 3*K*D + 2*K, by positivity, ?_⟩
  intro r hr p q hp hq
  let a : ℂ := r - s
  let b : ℂ := (r : ℂ) - 5/2
  let g := windowSignal p q a b
  let j := gateCut p q
  have hcG : HasCompactSupport g := windowSignal_compact hp hq a b
  have hsG : ContDiff ℝ ∞ g := windowSignal_smooth p q a b
  have hcJ : HasCompactSupport j := gateCut_compact hp hq
  have hsJ : ContDiff ℝ ∞ j := gateCut_smooth p q
  have hc1 := (contDiff_infty_iff_deriv.mp hsJ).2
  have hc2 := (contDiff_infty_iff_deriv.mp hc1).2
  have hs2 := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsG).2).2
  have hz {x : ℝ} (hx : x ≤ 0) : g =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [gt_mem_nhds (hx.trans_lt (by positivity : 0 < 1/p))] with t ht
    simp [g, windowSignal, gateCut_zero_left hp ht]
  have hJ1 : Integrable (fun x => |deriv j x|) :=
    (hc1.continuous.integrable_of_hasCompactSupport hcJ.deriv).norm
  have hJ2 : Integrable (fun x => |x| * |deriv (deriv j) x|) := by
    have hi : Integrable (fun x : ℝ => x * deriv (deriv j) x) :=
      (continuous_id.mul hc2.continuous).integrable_of_hasCompactSupport
        (hcJ.deriv.deriv.mul_left (f := id))
    simpa only [Real.norm_eq_abs, abs_mul] using hi.norm
  obtain ⟨hJ1val, hJ2val⟩ := hd p q hp hq
  constructor
  · calc
      (∫ x, ‖g x‖) ≤ ∫ x, 2 * T x := by
        apply integral_mono (hsG.continuous.integrable_of_hasCompactSupport hcG).norm (hT.const_mul 2)
        intro x
        change ‖g x‖ ≤ 2*T x
        by_cases hx : 0 < x
        · obtain ⟨h0, _⟩ := hk r hr.1 hr.2 x hx.le
          rw [hTpos hx]
          change ‖(gateCut p q x : ℂ) * expDiff a b x‖ ≤ _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact (mul_le_of_le_one_left (norm_nonneg _) (gateCut_unit _ _ _)).trans h0
        · simp [((hz (le_of_not_gt hx)).eq_of_nhds), T, hx]
      _ ≤ _ := by rw [integral_const_mul, hTval]; nlinarith [mul_nonneg hK.le hD]
  · let u := fun x : ℝ => K * (|x| * |deriv (deriv j) x|)
    let v := fun x : ℝ => (2*K) * |deriv j x|
    have hu : Integrable u := hJ2.const_mul K
    have hv : Integrable v := hJ1.const_mul (2*K)
    have huv : Integrable (fun x => u x + v x) := hu.add hv
    calc
      (∫ x, ‖deriv (deriv g) x‖) ≤ ∫ x, u x + v x + K*T x := by
        apply integral_mono (hs2.continuous.integrable_of_hasCompactSupport hcG.deriv.deriv).norm
          (huv.add (hT.const_mul K))
        intro x
        change ‖deriv (deriv g) x‖ ≤ u x + v x + K*T x
        by_cases hx : 0 < x
        · obtain ⟨_, hn, h1, h2⟩ := hk r hr.1 hr.2 x hx.le
          rw [hTpos hx]
          exact windowSignal_d2_bound (p := p) (q := q) (a := a) (b := b) (x := x) (K := K) hn h1 h2
        · have he := (hz (le_of_not_gt hx)).deriv.deriv_eq
          simp only [deriv_const', deriv_const] at he
          rw [he, norm_zero]
          simp only [u, v, T, indicator_of_notMem (show x ∉ Ioi 0 from hx), mul_zero, add_zero]
          positivity
      _ = K * (∫ x, |x| * |deriv (deriv j) x|) + (2*K)*(∫ x, |deriv j x|) + K*2 := by
        rw [integral_add huv (hT.const_mul K), integral_add hu hv]
        simp only [u, v, integral_const_mul, hTval]
      _ ≤ _ := by
        change (∫ x, |deriv j x|) ≤ D at hJ1val
        change (∫ x, |x| * |deriv (deriv j) x|) ≤ D at hJ2val
        nlinarith [mul_le_mul_of_nonneg_left hJ1val hK.le, mul_le_mul_of_nonneg_left hJ2val hK.le]

private theorem dom_fourier_step (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (c : ℂ) :
    (∫ x : ℝ, Complex.exp (c * x) * deriv g x) =
      - (c * ∫ x : ℝ, Complex.exp (c * x) * g x) := by
  let e := fun x : ℝ => Complex.exp (c * x)
  have he : Continuous e := by dsimp [e]; fun_prop
  have he' (x : ℝ) : HasDerivAt e (c * e x) x := by
    simpa [e, mul_comm] using (((hasDerivAt_id (x : ℂ)).const_mul c).cexp).comp_ofReal
  have hco := (contDiff_infty_iff_deriv.mp hg).2.continuous
  have h₁ : Integrable (e * deriv g) :=
    (he.mul hco).integrable_of_hasCompactSupport hc.deriv.mul_left
  have h₂ : Integrable ((fun x => c * e x) * g) :=
    ((continuous_const.mul he).mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left
  have h₃ : Integrable (e * g) :=
    (he.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := e) (v := g)
    (fun x _ => he' x)
    (fun x _ => (hg.differentiable (by simp) x).hasDerivAt) h₁ h₂ h₃
  simpa only [mul_assoc, integral_const_mul, e] using h

private theorem dom_fourier_l1 (g : ℝ → ℂ) (y : ℝ) :
    ‖∫ x : ℝ, Complex.exp (Complex.I * y * x) * g x‖ ≤ ∫ x : ℝ, ‖g x‖ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards with x
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem dom_fourier_bound (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (y : ℝ) :
    (1 + y^2) * ‖∫ x : ℝ, Complex.exp (Complex.I * y * x) * g x‖ ≤
      (∫ x : ℝ, ‖g x‖) + ∫ x : ℝ, ‖deriv (deriv g) x‖ := by
  have h₁ := dom_fourier_l1 g y
  have h₂ := dom_fourier_l1 (deriv (deriv g)) y
  rw [dom_fourier_step _ (contDiff_infty_iff_deriv.mp hg).2 hc.deriv,
    dom_fourier_step g hg hc] at h₂
  simp only [norm_neg, norm_mul, Complex.norm_I, Complex.norm_real, one_mul,
    Real.norm_eq_abs] at h₂
  rw [← mul_assoc, abs_mul_abs_self] at h₂
  linarith

private theorem dom_mellin_change (n : ℕ) (s w : ℂ) :
    mellin (regularizedTraceTest n s) (w - 1 / 2) =
    ∫ x : ℝ, Complex.exp (Complex.I * w.im * x) *
      (((Real.smoothTransition (((n : ℝ) + 1) * x - 1) *
          (1 - Real.smoothTransition ((((n : ℝ) + 1)⁻¹ * x) - 1)) : ℝ) : ℂ) *
        (Complex.exp (((w.re : ℂ) - s) * x) - Complex.exp (((w.re : ℂ) - 5/2) * x))) := by
  let f := fun t : ℝ => ((t : ℂ) ^ (w - 1 / 2 - 1)) • regularizedTraceTest n s t
  have hJ := integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s := (Set.univ : Set ℝ)) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (Real.exp_monotone.monotoneOn _) f
  rw [Set.image_univ, Real.range_exp, MeasureTheory.setIntegral_univ] at hJ
  change (∫ t in Ioi (0 : ℝ), f t) = _
  rw [hJ]
  apply integral_congr_ae
  filter_upwards with x
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpow (v : ℂ) : ((Real.exp x : ℝ) : ℂ) ^ v = Complex.exp ((x : ℂ) * v) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  by_cases hx : 0 < x
  · have h1 := Real.one_lt_exp_iff.mpr hx
    simp only [f, regularizedTraceTest, if_pos h1, traceLogCutoff, Real.log_exp,
      hpow, smul_eq_mul, Complex.real_smul]
    rw [Complex.ofReal_exp, show x / ((n : ℝ)+1) = ((n : ℝ)+1)⁻¹ * x by rw [div_eq_inv_mul]]
    let k : ℂ := ((Real.smoothTransition (((n : ℝ) + 1) * x - 1) *
      (1 - Real.smoothTransition (((n : ℝ) + 1)⁻¹ * x - 1)) : ℝ) : ℂ)
    change Complex.exp (x : ℂ) * (Complex.exp ((x : ℂ) * (w - 1 / 2 - 1)) *
        (k * (Complex.exp ((x : ℂ) * (1 / 2 - s)) - Complex.exp ((x : ℂ) * -2)))) = _
    have hE (v : ℂ) :
        (x : ℂ) + x * (w - 1/2 - 1) + x * v =
          Complex.I * w.im * x + ((w.re : ℂ) - 1/2 + v) * x := by
      linear_combination -(x : ℂ) * (Complex.re_add_im w)
    calc
      _ = k * (Complex.exp ((x : ℂ) + x * (w - 1/2 - 1) + x * (1/2-s)) -
          Complex.exp ((x : ℂ) + x * (w - 1/2 - 1) + x * -2)) := by
          simp only [Complex.exp_add]; ring
      _ = _ := by
          rw [hE, hE, show (w.re : ℂ) - 1/2 + (1/2-s) = w.re - s by ring,
            show (w.re : ℂ) - 1/2 + -2 = w.re - 5/2 by ring]
          simp only [Complex.exp_add]
          change k * (_ - _) = _ * (k * _)
          ring
  · have hn1 : ¬ 1 < Real.exp x := fun h => hx (Real.one_lt_exp_iff.mp h)
    have hleft : ((n : ℝ) + 1)*x - 1 ≤ 0 :=
      by linarith [mul_nonpos_of_nonneg_of_nonpos hn.le (le_of_not_gt hx)]
    simp [f, regularizedTraceTest, hn1, Real.smoothTransition.zero_of_nonpos hleft]

theorem solution (α : ℝ)
    (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ρ : ZetaZerosInTraceStrip α),
      ‖zetaTraceTerm (regularizedTraceTest n s) α ρ‖ ≤ C * zeroDecayWeight α ρ := by
  obtain ⟨B, hB, hbound⟩ := windowSignal_bounds s hs
  refine ⟨B+B, by positivity, ?_⟩
  intro n ρ
  let p : ℝ := (n : ℝ) + 1
  let r := (ρ : ℂ).re
  let y := (ρ : ℂ).im
  let a : ℂ := r - s
  let b : ℂ := r - 5/2
  let g := windowSignal p p⁻¹ a b
  have hp : 0 < p := by dsimp [p]; positivity
  have hq := inv_pos.mpr hp
  have hr : r ∈ Ioo (0 : ℝ) 1 := ⟨ρ.prop.2.1, ρ.prop.2.2.1⟩
  obtain ⟨h₀, h₂⟩ := hbound r hr p p⁻¹ hp hq
  have hM : mellin (regularizedTraceTest n s) ((ρ : ℂ) - 1/2) =
      ∫ x : ℝ, Complex.exp (Complex.I * y * x) * g x :=
    dom_mellin_change n s ρ
  have h := dom_fourier_bound g (windowSignal_smooth p p⁻¹ a b)
    (windowSignal_compact hp hq a b) y
  rw [← hM] at h
  have hN : ‖mellin (regularizedTraceTest n s) ((ρ : ℂ) - 1/2)‖ ≤
      (B+B) / (1+y^2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [mul_comm]
    exact h.trans (add_le_add h₀ h₂)
  have hm := mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg (α := ℝ)
    (analyticOrderNatAt riemannZeta (ρ : ℂ)))
  simpa only [zetaTraceTerm, norm_mul, Complex.norm_natCast, zeroDecayWeight, y, div_eq_mul_inv,
    mul_left_comm, mul_assoc] using hm
