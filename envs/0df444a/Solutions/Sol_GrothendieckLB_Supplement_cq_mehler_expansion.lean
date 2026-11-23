-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_mehler_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T18:35:12.9408+00:00
-- url     : https://prove2.me/submissions/65ebaf07-bf44-4bea-bd11-5af81f67f00a

import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_9
import Theorems.Thm_OAI_FiniteEntropySeparation_hermite_orthogonality
import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Definitions.Def_GrothendieckLB_Supplement_cqA
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory Polynomial Real GrothendieckLB GrothendieckLB.Supplement
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1000000
namespace IntegratedMehler

private abbrev X := ℝ × ℝ
private noncomputable def pdf := gaussianPDFReal 0 1
private noncomputable def hp (n : ℕ) (x : ℝ) := QuadSDE.hermiteN n x * pdf x
private noncomputable def density (r x y : ℝ) : ℝ := 1/(2*π*√(1-r^2)) *
  exp (-(x^2-2*r*x*y+y^2)/(2*(1-r^2)))
private noncomputable def basis (a b : ℕ) (w : X) : ℝ := hp a w.1 * hp b w.2

private theorem poly_int (p : ℤ[X]) : Integrable fun x : ℝ => aeval x p * pdf x := by
  have hi : Integrable fun x : ℝ => aeval x p * exp (-(x^2)/2) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have hi : Integrable (fun x : ℝ => aeval x p * exp (-(x^2)/2) + aeval x q * exp (-(x^2)/2)) := hp.add hq
      simpa only [map_add,add_mul] using hi
    | monomial n a =>
      have h : Integrable fun x : ℝ => x^n * exp (-(1/2:ℝ)*x^2) := by
        simpa only [rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/2)
          (lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg n))
      convert h.const_mul ((algebraMap ℤ ℝ) a) using 1
      funext x
      rw [aeval_monomial]
      ring_nf
  convert hi.const_mul ((√(2*π))⁻¹) using 1
  funext x
  simp [pdf, gaussianPDFReal]
  ring

private lemma hp_int (a : ℕ) : Integrable (hp a) := by
  convert (poly_int (hermite a)).div_const (√(a.factorial:ℝ)) using 1
  funext x
  unfold hp QuadSDE.hermiteN
  ring

private lemma hp_l1 (a : ℕ) : (∫ x, ‖hp a x‖) ≤ 1 := by
  let h := QuadSDE.hermiteN a
  have h2int : Integrable (fun x => (h x)^2 * pdf x) := by
    convert (poly_int ((hermite a)^2)).div_const (√(a.factorial:ℝ)^2) using 1
    funext x
    simp only [h,QuadSDE.hermiteN, map_pow, div_pow]
    ring
  have hor := OAI.FiniteEntropySeparation.hermite_orthogonality a a
  simp only [if_true, eval_mul, eval_map] at hor
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0)≠0)] at hor
  have h2eq : (∫ x, (h x)^2 * pdf x) = 1 := by
    have he (x : ℝ) : (h x)^2 * pdf x = (pdf x * (aeval x (hermite a) * aeval x (hermite a)))/(a.factorial : ℝ) := by
      simp only [h, QuadSDE.hermiteN, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    simp_rw [he, integral_div]
    change (∫ x, pdf x * (aeval x (hermite a) * aeval x (hermite a))) = (a.factorial:ℝ) at hor
    rw [hor,div_self (by positivity)]
  have hv : (∫ x, pdf x) = 1 := integral_gaussianPDFReal_eq_one _ (by norm_num)
  have hpdf (x : ℝ) : 0 ≤ pdf x := gaussianPDFReal_nonneg 0 1 x
  have hpdfint : Integrable pdf := integrable_gaussianPDFReal 0 1
  have hbound := integral_mono ((hp_int a).norm.const_mul 2) (h2int.add hpdfint)
    (show (fun x => 2*‖hp a x‖) ≤ (fun x => (h x)^2*pdf x + pdf x) from by
      intro x
      change 2 * ‖h x * pdf x‖ ≤ (h x)^2*pdf x + pdf x
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hpdf x)]
      have hx : 2 * |h x| ≤ (h x)^2 + 1 := by nlinarith [sq_nonneg (|h x|-1), sq_abs (h x)]
      nlinarith only [mul_le_mul_of_nonneg_right hx (hpdf x)])
  change (∫ x, 2 * ‖hp a x‖) ≤ ∫ x, (h x)^2 * pdf x + pdf x at hbound
  rw [integral_const_mul,integral_add h2int hpdfint,h2eq,hv] at hbound
  linarith

private lemma measF (η s₃ s₅ : ℝ) : Measurable (fun w : X => cqF η s₃ s₅ w.1 w.2) := by
  unfold cqF
  exact Measurable.ite (measurableSet_le measurable_const (by change Measurable (fun w : X => w.1 + _*((w.2^3-3*w.2)/Real.sqrt 6)); fun_prop)) measurable_const measurable_const

private lemma signF (η s₃ s₅ w t : ℝ) : ‖cqF η s₃ s₅ w t‖ = 1 := by
  unfold cqF
  split <;> simp

private noncomputable def leg (η s₃ s₅ : ℝ) (a b : ℕ) (w : X) := cqF η s₃ s₅ w.1 w.2 * basis a b w

private lemma leg_norm (η s₃ s₅ : ℝ) (a b : ℕ) (w : X) :
    ‖leg η s₃ s₅ a b w‖ = ‖hp a w.1‖ * ‖hp b w.2‖ := by
  simp only [leg,basis,norm_mul,signF,one_mul]

private lemma leg_int (η s₃ s₅ : ℝ) (a b : ℕ) : Integrable (leg η s₃ s₅ a b) := by
  apply ((hp_int a).norm.mul_prod (hp_int b).norm).mono'
  · have hc (n : ℕ) : Continuous (hp n) := by
      unfold hp QuadSDE.hermiteN pdf gaussianPDFReal
      fun_prop
    have hbas : Measurable (basis a b) :=
      ((hc a).measurable.comp measurable_fst).mul ((hc b).measurable.comp measurable_snd)
    exact ((measF η s₃ s₅).mul hbas).aestronglyMeasurable
  · exact ae_of_all _ fun x => (leg_norm η s₃ s₅ a b x).le

private lemma leg_l1 (η s₃ s₅ : ℝ) (a b : ℕ) : (∫ w, ‖leg η s₃ s₅ a b w‖) ≤ 1 := by
  simp only [leg_norm]
  rw [Measure.volume_eq_prod, integral_prod_mul (fun x => ‖hp a x‖) (fun x => ‖hp b x‖)]
  exact (mul_le_mul (hp_l1 a) (hp_l1 b) (integral_nonneg fun x => norm_nonneg _) zero_le_one).trans_eq (one_mul _)

private lemma leg_eq (η s₃ s₅ : ℝ) (a b : ℕ) : (∫ w, leg η s₃ s₅ a b w) = cqA η s₃ s₅ a b := by
  rw [Measure.volume_eq_prod,integral_prod _ (show Integrable _ _ from leg_int η s₃ s₅ a b)]
  unfold cqA
  congr 1
  ext w
  congr 1
  ext x
  dsimp [leg,basis,hp,pdf]
  ring

private lemma ab_le (η s₃ s₅ : ℝ) (a b : ℕ) : |cqA η s₃ s₅ a b| ≤ 1 := by
  rw [← leg_eq,← Real.norm_eq_abs]
  exact (norm_integral_le_integral_norm _).trans (leg_l1 _ _ _ _ _)

private lemma density_mehler (r x y : ℝ) (hr : |r| < 1) :
    HasSum (fun n : ℕ => r^n * hp n x * hp n y) (density r x y) := by
  let Xv : PrivateAgnosticHalfspace.Gaussian.Vec 1 := WithLp.toLp 2 (fun _ => x)
  let Yv : PrivateAgnosticHalfspace.Gaussian.Vec 1 := WithLp.toLp 2 (fun _ => y)
  have h := PrivateAgnosticHalfspace.Gaussian.lemma_B_9 1 Xv Yv r (abs_lt.mp hr)
  have h' := ( (Equiv.funUnique (Fin 1) ℕ).symm.hasSum_iff).2 h
  have hnormX : ‖Xv‖^2 = x^2 := by simp [EuclideanSpace.real_norm_sq_eq,Xv]
  have hnormY : ‖Yv‖^2 = y^2 := by simp [EuclideanSpace.real_norm_sq_eq,Yv]
  have hinn : inner ℝ Xv Yv = x*y := by simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Xv,Yv,mul_comm]
  rw [hnormX,hnormY,hinn] at h'
  have hg : ∀ n : ℕ, (fun κ : Fin 1 → ℕ => r ^ PrivateAgnosticHalfspace.Gaussian.degree κ *
        PrivateAgnosticHalfspace.Gaussian.hermite 1 κ Xv * PrivateAgnosticHalfspace.Gaussian.hermite 1 κ Yv)
        ((Equiv.funUnique (Fin 1) ℕ).symm n) = r^n * QuadSDE.hermiteN n x * QuadSDE.hermiteN n y := by
    intro n
    simp [PrivateAgnosticHalfspace.Gaussian.degree,PrivateAgnosticHalfspace.Gaussian.hermite, Xv,Yv,
      Equiv.funUnique,AMPLowDeg.RankOne.hermNorm, QuadSDE.hermiteN, eval_map]
    rfl
  have hp' : 0 < 1-r^2 := by nlinarith [(abs_lt.mp hr).1,(abs_lt.mp hr).2]
  have he : ((1-r^2)^(-(1:ℝ)/2)* exp ((2*r*x*y-r^2*(x^2+y^2))/(2*(1-r^2)))) * (pdf x * pdf y) = density r x y := by
    have ha : (2*r*x*y-r^2*(x^2+y^2))/(2*(1-r^2)) + (-(x^2)/2 + -(y^2)/2) =
        -(x^2-2*r*x*y+y^2)/(2*(1-r^2)) := by field_simp [hp'.ne']; ring
    have hpdf (v : ℝ) : pdf v = (√(2*π))⁻¹ * exp (-(v^2)/2) := by simp [pdf,gaussianPDFReal]
    have hpow : (1-r^2)^(-(1:ℝ)/2) = (√(1-r^2))⁻¹ := by
      rw [neg_div,Real.rpow_neg hp'.le,← Real.sqrt_eq_rpow]
    simp only [density,hpdf,hpow,← ha, Real.exp_add]
    field_simp [Real.pi_ne_zero, Real.sqrt_ne_zero'.mpr hp', Real.sqrt_ne_zero'.mpr (by positivity : 0 < 2*π)]
    nlinarith only [Real.sq_sqrt (show 0 ≤ 2*π by positivity)]
  rw [← he]
  norm_num only [Nat.cast_one] at h'
  rw [← mul_assoc (2*r) x y] at h'
  rw [← neg_div] at h'
  apply (h'.mul_right (pdf x * pdf y)).congr_fun
  intro n
  dsimp only [Function.comp_apply]
  have hh := hg n
  dsimp only at hh
  rw [hh]
  unfold hp
  ring

private noncomputable def envelope (x : ℝ) := exp (-(1/4:ℝ)*x^2)
private noncomputable def constant (r : ℝ) := 1/(2*π*√(1-r^2))

private lemma density_le (r x y : ℝ) (hr : |r| < 1) : ‖density r x y‖ ≤ constant r * (envelope x*envelope y) := by
  have h1 : 0 < 1+r := by linarith [(abs_lt.mp hr).1]
  have h2 : 0 < 1-r := by linarith [(abs_lt.mp hr).2]
  have hs : 0 < 1-r^2 := by nlinarith [mul_pos h1 h2]
  have hplus : (1/2:ℝ) ≤ 1/(1+r) := (le_div_iff₀ h1).mpr (by linarith [(abs_lt.mp hr).2])
  have hminus : (1/2:ℝ) ≤ 1/(1-r) := (le_div_iff₀ h2).mpr (by linarith [(abs_lt.mp hr).1])
  have hid : (x^2-2*r*x*y+y^2)/(2*(1-r^2)) = ((x+y)^2/4)*(1/(1+r)) + ((x-y)^2/4)*(1/(1-r)) := by
    field_simp [hs.ne',h1.ne',h2.ne'] <;> ring
  unfold density constant envelope
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rw [neg_div, hid]
  nlinarith only [mul_le_mul_of_nonneg_left hplus (sq_nonneg (x+y)),
    mul_le_mul_of_nonneg_left hminus (sq_nonneg (x-y))]

private noncomputable def joint (η s₃ s₅ r t : ℝ) (x y : X) :=
  cqF η s₃ s₅ x.1 x.2 * cqF η s₃ s₅ y.1 y.2 * density r x.1 y.1 * density (-t) x.2 y.2

private lemma joint_int (η s₃ s₅ r t : ℝ) (hr : |r| < 1) (ht : |t| < 1) :
    Integrable (Function.uncurry (joint η s₃ s₅ r t)) := by
  have he : Integrable envelope := integrable_exp_neg_mul_sq (by norm_num : 0 < (1/4:ℝ))
  let e (x : X) := envelope x.1 * envelope x.2
  have hx : Integrable e := he.mul_prod he
  apply ((hx.mul_prod hx).const_mul (constant r * constant (-t))).mono'
  · have h1 : Measurable (fun z : X×X => density r z.1.1 z.2.1) := by
      unfold density
      fun_prop
    have h2 : Measurable (fun z : X×X => density (-t) z.1.2 z.2.2) := by
      unfold density
      fun_prop
    change AEStronglyMeasurable (fun z : X×X =>
        cqF η s₃ s₅ z.1.1 z.1.2 * cqF η s₃ s₅ z.2.1 z.2.2 *
        density r z.1.1 z.2.1 * density (-t) z.1.2 z.2.2) volume
    exact (((((measF η s₃ s₅).comp measurable_fst).mul ((measF η s₃ s₅).comp measurable_snd)).mul h1).mul h2).aestronglyMeasurable
  · apply ae_of_all
    intro p
    simp only [Function.uncurry,joint,norm_mul,signF,one_mul]
    have h := mul_le_mul (density_le r p.1.1 p.2.1 hr)
      (density_le (-t) p.1.2 p.2.2 (by simpa using ht)) (norm_nonneg _)
      (by unfold constant envelope; positivity)
    exact h.trans_eq (by dsimp [e]; ring)

private lemma corr_eq (η s₃ s₅ t : ℝ) :
    cqCorr η s₃ s₅ t = π/2 * ∫ x : X, ∫ y : X, joint η s₃ s₅ ((cqRhoPoly s₃ s₅).eval t) t x y := by
  let r := (cqRhoPoly s₃ s₅).eval t
  let e := @MeasurableEquiv.finTwoArrow ℝ _
  let flip := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
  have hf : MeasurePreserving flip volume volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg _)
  have he : MeasurePreserving e volume volume := volume_preserving_finTwoArrow ℝ
  have hy (x y : ℝ) : cqF η s₃ s₅ x (-y) = cqG η s₃ s₅ x y := by
    unfold cqF cqG
    change (if 0 ≤ x + _ * (((-y)^3-3*(-y))/√6) then _ else _) =
      (if 0 ≤ x - _ * ((y^3-3*y)/√6) then _ else _)
    ring_nf
  have hd (x y : ℝ) : density (-t) x (-y) = density t x y := by unfold density; ring_nf
  unfold cqCorr multiCorr
  congr 1
  rw [← he.integral_comp' (fun x : X => ∫ y : X, joint η s₃ s₅ r t x y)]
  apply integral_congr_ae
  filter_upwards with x
  rw [← hf.integral_comp' (joint η s₃ s₅ r t (e x))]
  rw [← he.integral_comp' (fun y : X => joint η s₃ s₅ r t (e x) (flip y))]
  apply integral_congr_ae
  filter_upwards with y
  change _ = cqF η s₃ s₅ (x 0) (x 1) * cqF η s₃ s₅ (y 0) (-(y 1)) *
    density r (x 0) (y 0) * density (-t) (x 1) (-(y 1))
  rw [hy,hd]
  simp only [Fin.prod_univ_two,GrothendieckConstant.gaussianPairDensity,Fin.prod_univ_one,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons, r, density]
  ring

private lemma rho_small (s₃ s₅ t : ℝ) (ht : |t| < 1) : |(cqRhoPoly s₃ s₅).eval t| < 1 := by
  let V := 1+s₃^2+s₅^2
  have hV : 0<V := by dsimp [V]; positivity
  have h3 := pow_le_one₀ (abs_nonneg t) ht.le (n:=3)
  have h5 := pow_le_one₀ (abs_nonneg t) ht.le (n:=5)
  simp only [cqRhoPoly,eval_mul,eval_C,eval_add,eval_sub,eval_X, eval_pow,abs_mul,
    abs_div,abs_one, abs_of_pos hV]
  change 1/|V| * |t-s₃^2*t^3+s₅^2*t^5| < 1
  rw [abs_of_pos hV,one_div,← div_eq_inv_mul,div_lt_iff₀ hV,one_mul]
  have hh : |t-s₃^2*t^3| ≤ |t| + |s₃^2*t^3| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le t (-(s₃^2*t^3))
  have h := (abs_add_le (t-s₃^2*t^3) (s₅^2*t^5)).trans (add_le_add hh le_rfl)
  simp only [abs_mul, abs_pow, sq_abs] at h
  dsimp [V]
  nlinarith only [h,ht,mul_le_mul_of_nonneg_left h3 (sq_nonneg s₃),mul_le_mul_of_nonneg_left h5 (sq_nonneg s₅)]

end IntegratedMehler
open IntegratedMehler

theorem solution (η s₃ s₅ : ℝ) :
    (∀ a b : ℕ, |cqA η s₃ s₅ a b| ≤ 1) ∧
    (∀ t : ℝ, |t| < 1 →
      HasSum (fun p : ℕ × ℕ => Real.pi / 2 * (cqA η s₃ s₅ p.1 p.2) ^ 2 *
        ((cqRhoPoly s₃ s₅).eval t) ^ p.1 * (-t) ^ p.2) (cqCorr η s₃ s₅ t)) := by
  refine ⟨ab_le η s₃ s₅, ?_⟩
  intro t ht
  let r := (cqRhoPoly s₃ s₅).eval t
  have hr : |r|<1 := rho_small s₃ s₅ t ht
  let S := leg η s₃ s₅
  let w (p : ℕ × ℕ) := r^p.1 * (-t)^p.2
  let F (p : ℕ × ℕ) (xy : X × X) := w p * (S p.1 p.2 xy.1 * S p.1 p.2 xy.2)
  have hi (p : ℕ × ℕ) : Integrable (F p) :=
    ((leg_int η s₃ s₅ p.1 p.2).mul_prod (leg_int η s₃ s₅ p.1 p.2)).const_mul _
  have hf (x y : X) : HasSum (fun p => F p (x,y)) (joint η s₃ s₅ r t x y) := by
    have h1 := density_mehler r x.1 y.1 hr
    have h2 := density_mehler (-t) x.2 y.2 (by simpa using ht)
    have h := (h1.mul h2 (summable_mul_of_summable_norm h1.summable.norm h2.summable.norm)).mul_left
      (cqF η s₃ s₅ x.1 x.2 * cqF η s₃ s₅ y.1 y.2)
    have heq : HasSum (fun p : ℕ × ℕ => F p (x,y))
        ((cqF η s₃ s₅ x.1 x.2 * cqF η s₃ s₅ y.1 y.2) * (density r x.1 y.1 * density (-t) x.2 y.2)) := by
      apply h.congr_fun
      intro p
      dsimp only [F,w,S,leg,basis]
      ring
    simpa only [joint,mul_assoc] using heq
  have hweight : Summable fun p : ℕ × ℕ => |r|^p.1 * |t|^p.2 :=
    (summable_geometric_of_lt_one (abs_nonneg _) hr).mul_of_nonneg (summable_geometric_of_lt_one (abs_nonneg _) ht)
      (fun _ => by positivity) (fun _ => by positivity)
  have hs : Summable (fun p : ℕ × ℕ => ∫ xy, ‖F p xy‖) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) _ hweight
    intro p
    simp only [F,w,norm_mul,Real.norm_eq_abs,abs_pow,abs_neg,integral_const_mul]
    rw [show (∫ xy : X×X, |S p.1 p.2 xy.1| * |S p.1 p.2 xy.2|) =
        (∫ x, |S p.1 p.2 x|) * ∫ y, |S p.1 p.2 y| from
      integral_prod_mul (fun x => |S p.1 p.2 x|) (fun y => |S p.1 p.2 y|)]
    have hl := leg_l1 η s₃ s₅ p.1 p.2
    simp only [Real.norm_eq_abs] at hl
    apply mul_le_of_le_one_right (by positivity)
    exact (mul_le_mul hl hl (integral_nonneg fun _ => abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have he (p : ℕ × ℕ) : (∫ xy, F p xy) = w p * (cqA η s₃ s₅ p.1 p.2)^2 := by
    simp only [F,integral_const_mul,pow_two]
    rw [show (∫ xy : X×X, S p.1 p.2 xy.1 * S p.1 p.2 xy.2) =
        (∫ x, S p.1 p.2 x) * ∫ y, S p.1 p.2 y from integral_prod_mul (S p.1 p.2) (S p.1 p.2)]
    simp only [S,leg_eq]
  have h := hasSum_integral_of_summable_integral_norm hi hs
  have hsum (xy : X × X) : (∑' p, F p xy) = joint η s₃ s₅ r t xy.1 xy.2 := (hf xy.1 xy.2).tsum_eq
  simp only [he,hsum] at h
  have hFub : (∫ xy : X×X, joint η s₃ s₅ r t xy.1 xy.2) = ∫ x : X, ∫ y : X, joint η s₃ s₅ r t x y :=
    integral_prod (Function.uncurry (joint η s₃ s₅ r t)) (joint_int η s₃ s₅ r t hr ht)
  rw [hFub] at h
  rw [corr_eq]
  apply (h.mul_left (π/2)).congr_fun
  intro p
  dsimp [w,r]
  ring
