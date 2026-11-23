-- Prove2me | solution 1 for GrothendieckLB.linear_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:54:48.289989+00:00
-- url     : https://prove2.me/submissions/84033074-c0db-4d8f-9359-0afe9022b605

import Mathlib
import Definitions.Def_GrothendieckLB_IsSignFn
import Definitions.Def_GrothendieckLB_p1Norm
import Definitions.Def_ABPOnline_cG

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

namespace KG

noncomputable def phiK (k : ℕ) (x : Fin k → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

lemma phiK_nonneg (k : ℕ) (x : Fin k → ℝ) : 0 ≤ phiK k x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i)

lemma measurable_phiK (k : ℕ) : Measurable (phiK k) := by
  unfold phiK
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

lemma pi_gauss (k : ℕ) :
    Measure.pi (fun _ : Fin k => gaussianReal 0 1) =
      (volume : Measure (Fin k → ℝ)).withDensity (fun x => ENNReal.ofReal (phiK k x)) := by
  refine Measure.pi_eq (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : Fin k → ℝ, (Set.univ.pi s).indicator (fun x => ENNReal.ofReal (phiK k x)) x
      = ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      unfold phiK
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
      simp
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hind]
  have hint : Integrable (fun x : Fin k → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod fun i =>
      (integrable_gaussianPDFReal 0 1).indicator (hs i)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x =>
      Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  rw [volume_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun y => Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [integral_indicator (hs i), gaussianReal_apply 0 one_ne_zero (s i)]
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
    (Filter.Eventually.of_forall fun y => gaussianPDFReal_nonneg 0 1 y)]
  rfl

lemma integral_phiK (k : ℕ) (F : (Fin k → ℝ) → ℝ) :
    ∫ x, phiK k x * F x = ∫ x, F x ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) := by
  rw [pi_gauss, integral_withDensity_eq_integral_toReal_smul (measurable_phiK k).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (phiK_nonneg k x)]

lemma gauss_abs_moment (q : ℝ) (hq : -1 < q) :
    ∫ t, |t| ^ q ∂(gaussianReal 0 1) =
      2 * ((1 / Real.sqrt (2 * π)) * ((1 / 2 : ℝ) ^ (-(q + 1) / 2) * (1 / 2) * Gamma ((q + 1) / 2))) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h1 : ∀ t : ℝ, gaussianPDFReal 0 1 t • |t| ^ q =
      (fun u : ℝ => (1 / Real.sqrt (2 * π)) * (u ^ q * Real.exp (-(1 / 2) * u ^ (2 : ℝ)))) |t| := by
    intro t
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    rw [Real.rpow_two, sq_abs]
    ring_nf
  simp_rw [h1]
  rw [integral_comp_abs (f := fun u : ℝ => (1 / Real.sqrt (2 * π)) * (u ^ q * Real.exp (-(1 / 2) * u ^ (2 : ℝ))))]
  rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_rpow (by norm_num) hq (by norm_num)]

lemma gauss_abs_one : ∫ t, |t| ∂(gaussianReal 0 1) = Real.sqrt (2 / π) := by
  have h := gauss_abs_moment 1 (by norm_num)
  simp only [Real.rpow_one] at h
  rw [h]
  norm_num [Real.Gamma_one]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hp : Real.sqrt π ≠ 0 := by positivity
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp
  nlinarith [hs]

open scoped RealInnerProductSpace

lemma proj_law (k : ℕ) (v : Fin k → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (fun x => ∑ i, v i * x i) = gaussianReal 0 1 := by
  set u : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 v
  have hu : ‖u‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simpa [u, Real.norm_eq_abs, sq_abs] using hv
  have hfun : (fun x : Fin k → ℝ => ∑ i, v i * x i) = (fun y : EuclideanSpace ℝ (Fin k) => ⟪y, u⟫) ∘ (WithLp.toLp 2) := by
    funext x
    simp [u, PiLp.inner_apply]
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian]
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin k)) := innerSL ℝ u
  have hL : ‖L‖ = 1 := by simp [L, hu]
  have hm : (stdGaussian (EuclideanSpace ℝ (Fin k))).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hL]
    norm_num
  convert hm using 1
  congr 1
  ext y
  simpa [L] using (real_inner_comm u y)

lemma proj_abs_moment (k : ℕ) (v : Fin k → ℝ) (hv : ∑ i, v i ^ 2 = 1) (n : ℕ) :
    ∫ x, phiK k x * |∑ i, v i * x i| ^ n = ∫ t, |t| ^ n ∂(gaussianReal 0 1) := by
  have hm : Measurable (fun x : Fin k → ℝ => ∑ i, v i * x i) :=
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _
  rw [integral_phiK]
  calc ∫ x, |∑ i, v i * x i| ^ n ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = ∫ t, |t| ^ n ∂((Measure.pi fun _ : Fin k => gaussianReal 0 1).map (fun x => ∑ i, v i * x i)) :=
        (integral_map hm.aemeasurable (continuous_abs.pow n).aestronglyMeasurable).symm
    _ = ∫ t, |t| ^ n ∂(gaussianReal 0 1) := by rw [proj_law k v hv]

lemma poly_exp_le (k : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    500 * (1 + A + k) ^ 3 * Real.exp (-(A / 4))
      ≤ 2000 * ((1 + k) ^ 3 + 3072) * Real.exp (-(A / 8)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcube : (1 + A + k) ^ 3 ≤ 4 * ((1 + k) ^ 3 + A ^ 3) := by
    nlinarith [sq_nonneg (1 + k - A), mul_nonneg (add_nonneg zero_le_one hk) hA,
      mul_nonneg (mul_nonneg (add_nonneg zero_le_one hk) hA) (sq_nonneg (1 + k - A))]
  have hA3 : A ^ 3 ≤ 3072 * Real.exp (A / 8) := by
    have := Real.pow_div_factorial_le_exp (A / 8) (by positivity) 3
    norm_num [Nat.factorial] at this
    nlinarith
  have he1 : 1 ≤ Real.exp (A / 8) := Real.one_le_exp (by positivity)
  have hsplit : Real.exp (-(A / 4)) = (Real.exp (A / 8))⁻¹ * Real.exp (-(A / 8)) := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  have hpos : 0 < Real.exp (-(A / 8)) := Real.exp_pos _
  have key : (1 + A + k) ^ 3 * (Real.exp (A / 8))⁻¹ ≤ 4 * ((1 + k) ^ 3 + 3072) := by
    rw [mul_inv_le_iff₀ (Real.exp_pos _)]
    have : (0 : ℝ) ≤ (1 + k) ^ 3 := by positivity
    nlinarith
  rw [hsplit]
  have := mul_le_mul_of_nonneg_right key hpos.le
  nlinarith

lemma gaussianPDFReal_std (s : ℝ) :
    gaussianPDFReal 0 1 s = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(s ^ 2 / 2)) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

lemma phiK_le_exp {k : ℕ} (x : Fin k → ℝ) : phiK k x ≤ Real.exp (-((∑ i, x i ^ 2) / 2)) := by
  unfold phiK
  rw [show -((∑ i, x i ^ 2) / 2) = ∑ i, -(x i ^ 2 / 2) by rw [Finset.sum_div, Finset.sum_neg_distrib],
    Real.exp_sum]
  refine Finset.prod_le_prod (fun i _ => gaussianPDFReal_nonneg _ _ _) fun i _ => ?_
  rw [gaussianPDFReal_std]
  have : 1 ≤ Real.sqrt (2 * π) := by
    rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  calc (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x i ^ 2 / 2)) ≤ 1 * Real.exp (-(x i ^ 2 / 2)) := by
        gcongr; exact inv_le_one_of_one_le₀ this
    _ = _ := one_mul _

lemma integrable_exp_Q (k : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : Fin k → ℝ => Real.exp (-(b * ∑ i, x i ^ 2))) := by
  have h1 : Integrable (fun x : Fin k → ℝ => ∏ i, Real.exp (-b * x i ^ 2)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ s => Real.exp (-b * s ^ 2))
      fun _ => integrable_exp_neg_mul_sq hb
  refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma integrable_poly_phi {k : ℕ} (h p : (Fin k → ℝ) → ℝ) (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) (hp : Measurable p) (C : ℝ) (hC : 0 ≤ C)
    (hpC : ∀ x, |p x| ≤ C * (1 + ∑ i, x i ^ 2) ^ 3) :
    Integrable (fun x => h x * p x * phiK k x) := by
  refine ((integrable_exp_Q k (1 / 4) (by norm_num)).const_mul (C * (2000 * 3073 / 500))).mono'
    ((hh.mul hp).mul (measurable_phiK k)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  set Q := ∑ i, x i ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hphi := phiK_le_exp x
  have hphi0 := phiK_nonneg k x
  have key := poly_exp_le 0 (A := 2 * Q) (by positivity)
  simp only [Nat.cast_zero, add_zero] at key
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hphi0]
  have h1 : (1 + Q) ^ 3 ≤ (1 + 2 * Q) ^ 3 := by gcongr; linarith
  have e1 : -(2 * Q / 4) = -(Q / 2) := by ring
  have e2 : -(2 * Q / 8) = -(1 / 4 * Q) := by ring
  rw [e1, e2] at key
  calc |h x| * |p x| * phiK k x ≤ 1 * (C * (1 + Q) ^ 3) * Real.exp (-(Q / 2)) := by
        gcongr
        · exact hb x
        · exact hpC x
    _ ≤ C * ((1 + 2 * Q) ^ 3 * Real.exp (-(Q / 2))) := by
        rw [one_mul, mul_assoc]; gcongr
    _ ≤ C * (2000 * (1 + 3072) / 500 * Real.exp (-(1 / 4 * Q))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        norm_num at key ⊢; linarith
    _ = _ := by norm_num; ring

lemma abs_coord_le {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : |x i| ≤ 1 + ∑ j, x j ^ 2 := by
  have : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x i + 1 / 2), sq_nonneg (x i - 1 / 2)]

lemma one_le_oneQ {k : ℕ} (x : Fin k → ℝ) : 1 ≤ 1 + ∑ j, x j ^ 2 := by
  have := Finset.sum_nonneg (s := Finset.univ) fun j _ => sq_nonneg (x j); linarith

lemma abs_coord_le3 {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : |x i| ≤ 1 * (1 + ∑ j, x j ^ 2) ^ 3 := by
  have h1 := one_le_oneQ x
  have := abs_coord_le x i
  nlinarith [pow_le_pow_right₀ h1 (show 1 ≤ 3 by norm_num), pow_one (1 + ∑ j, x j ^ 2)]

noncomputable def mom1 {k : ℕ} (h : (Fin k → ℝ) → ℝ) (i : Fin k) : ℝ := ∫ x, h x * x i * phiK k x

lemma integrable_mom1 {k : ℕ} (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (i : Fin k) : Integrable (fun x => h x * x i * phiK k x) :=
  integrable_poly_phi h (fun x => x i) hh hb (measurable_pi_apply i) 1 zero_le_one
    fun x => abs_coord_le3 x i

noncomputable def proj {k : ℕ} (v x : Fin k → ℝ) : ℝ := ∑ i, v i * x i

lemma measurable_proj {k : ℕ} (v : Fin k → ℝ) : Measurable (proj v) := by
  unfold proj; fun_prop

lemma abs_proj_le {k : ℕ} (v x : Fin k → ℝ) :
    |proj v x| ≤ (∑ i, |v i|) * (1 + ∑ j, x j ^ 2) := by
  unfold proj
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_coord_le x i) (abs_nonneg _)

lemma abs_proj_pow_le {k : ℕ} (v x : Fin k → ℝ) (n : ℕ) (hn : n ≤ 3) :
    |proj v x ^ n| ≤ (1 + ∑ i, |v i|) ^ 3 * (1 + ∑ j, x j ^ 2) ^ 3 := by
  have h1 := one_le_oneQ x
  have hv : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hp : |proj v x| ≤ (1 + ∑ i, |v i|) * (1 + ∑ j, x j ^ 2) :=
    (abs_proj_le v x).trans (by gcongr; linarith)
  have hge : 1 ≤ (1 + ∑ i, |v i|) * (1 + ∑ j, x j ^ 2) := by nlinarith
  rw [abs_pow, ← mul_pow]
  calc |proj v x| ^ n ≤ ((1 + ∑ i, |v i|) * (1 + ∑ j, x j ^ 2)) ^ n := by gcongr
    _ ≤ _ := pow_le_pow_right₀ hge hn

lemma integrable_proj_pow {k : ℕ} (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (v : Fin k → ℝ) (n : ℕ) (hn : n ≤ 3) :
    Integrable (fun x => h x * proj v x ^ n * phiK k x) :=
  integrable_poly_phi h _ hh hb ((measurable_proj v).pow_const n) _ (by positivity)
    fun x => abs_proj_pow_le v x n hn

lemma integrable_abs_proj_pow {k : ℕ} (v : Fin k → ℝ) (n : ℕ) (hn : n ≤ 3) :
    Integrable (fun x => phiK k x * |proj v x| ^ n) := by
  have := integrable_poly_phi (fun _ => (1 : ℝ)) (fun x => |proj v x| ^ n) measurable_const
    (fun _ => by simp) ((measurable_proj v).abs.pow_const n) ((1 + ∑ i, |v i|) ^ 3) (by positivity)
    fun x => by rw [abs_pow, abs_abs, ← abs_pow]; exact abs_proj_pow_le v x n hn
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only; ring

lemma moment_le_abs {k : ℕ} (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (v : Fin k → ℝ) (hv : ∑ i, v i ^ 2 = 1) (n : ℕ) (hn : n ≤ 3) :
    ∫ x, h x * proj v x ^ n * phiK k x ≤ ∫ t, |t| ^ n ∂(gaussianReal 0 1) := by
  rw [← proj_abs_moment k v hv n]
  refine integral_mono (integrable_proj_pow h hh hb v n hn) (integrable_abs_proj_pow v n hn)
    fun x => ?_
  have h0 := phiK_nonneg k x
  have : h x * proj v x ^ n ≤ |proj v x| ^ n := by
    calc h x * proj v x ^ n ≤ |h x * proj v x ^ n| := le_abs_self _
      _ = |h x| * |proj v x| ^ n := by rw [abs_mul, abs_pow]
      _ ≤ 1 * |proj v x| ^ n := by gcongr; exact hb x
      _ = _ := one_mul _
  show h x * proj v x ^ n * phiK k x ≤ phiK k x * |proj v x| ^ n
  nlinarith

lemma sum_mom1_eq {k : ℕ} (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (v : Fin k → ℝ) :
    ∑ i, v i * mom1 h i = ∫ x, h x * proj v x ^ 1 * phiK k x := by
  unfold mom1
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun i _ => (integrable_mom1 h hh hb i).const_mul (v i)]
  congr 1; ext x
  simp only [proj, pow_one, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end KG

namespace GrothendieckLB

lemma linearMoment_eq_mom1 {d : ℕ} (F : (Fin d → ℝ) → ℝ) (i : Fin d) :
    linearMoment F i = KG.mom1 F i := by
  rfl

lemma p1Norm_le_cG {d : ℕ} (F : (Fin d → ℝ) → ℝ) (hF : Measurable F)
    (hb : ∀ x, |F x| ≤ 1) : p1Norm F ≤ ABPOnline.cG := by
  set N : ℝ := ∑ i, KG.mom1 F i * KG.mom1 F i with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hnorm : p1Norm F = Real.sqrt N := by
    rw [p1Norm, p1Inner, hN]
    exact congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => by rw [linearMoment_eq_mom1 F i])
  rw [hnorm]
  rcases eq_or_lt_of_le hN0 with hzero | hpos
  · rw [← hzero, Real.sqrt_zero]
    exact Real.sqrt_nonneg _
  · set α : ℝ := Real.sqrt N with hαdef
    have hα : 0 < α := Real.sqrt_pos.mpr hpos
    have hαsq : α ^ 2 = N := Real.sq_sqrt hN0
    set v : Fin d → ℝ := fun i => KG.mom1 F i / α with hvdef
    have hv : ∑ i, v i ^ 2 = 1 := by
      simp only [hvdef, div_pow, ← Finset.sum_div, hαsq]
      rw [div_eq_one_iff_eq hpos.ne']
      exact Finset.sum_congr rfl fun i _ => sq _
    have hva : ∑ i, v i * KG.mom1 F i = α := by
      simp only [hvdef, div_mul_eq_mul_div, ← Finset.sum_div]
      rw [← hN, ← hαsq]
      field_simp
    have hαs : α ≤ Real.sqrt (2 / Real.pi) := by
      rw [← hva, KG.sum_mom1_eq F hF hb v]
      have hm := KG.moment_le_abs F hF hb v hv 1 (by norm_num)
      simp only [pow_one] at hm ⊢
      rwa [KG.gauss_abs_one] at hm
    exact hαs

lemma isSignFn_abs_le {d : ℕ} {F : (Fin d → ℝ) → ℝ} (hF : IsSignFn F) (x : Fin d → ℝ) :
    |F x| ≤ 1 := by
  rcases hF.2 x with hx | hx <;> simp [hx]

lemma abs_p1Inner_le {d : ℕ} (f g : (Fin d → ℝ) → ℝ) :
    |p1Inner f g| ≤ p1Norm f * p1Norm g := by
  let a : Fin d → ℝ := linearMoment f
  let b : Fin d → ℝ := linearMoment g
  have hcs : (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have ha : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsa : Real.sqrt (∑ i, a i ^ 2) ^ 2 = ∑ i, a i ^ 2 := Real.sq_sqrt ha
  have hsb : Real.sqrt (∑ i, b i ^ 2) ^ 2 = ∑ i, b i ^ 2 := Real.sq_sqrt hb
  have hprod : (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2)) ^ 2 =
      (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by rw [mul_pow, hsa, hsb]
  have hnonneg : 0 ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have habs : |∑ i, a i * b i| ≤
      Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith
  change |∑ i, a i * b i| ≤
    Real.sqrt (∑ i, a i * a i) * Real.sqrt (∑ i, b i * b i)
  simpa only [sq] using habs

end GrothendieckLB

open GrothendieckLB

theorem solution (d : ℕ) :
    (∀ F : (Fin d → ℝ) → ℝ, Measurable F → (∀ x, |F x| ≤ 1) → p1Norm F ≤ ABPOnline.cG) ∧
    (∀ f g : (Fin d → ℝ) → ℝ, IsSignFn f → IsSignFn g →
      |(Real.pi / 2) * p1Inner f g| ≤ 1) := by
  constructor
  · intro F hF hb
    exact p1Norm_le_cG F hF hb
  · intro f g hf hg
    have hν : 0 ≤ ABPOnline.cG := Real.sqrt_nonneg _
    have hνsq : ABPOnline.cG ^ 2 = 2 / Real.pi := by
      rw [ABPOnline.cG, Real.sq_sqrt]
      positivity
    have hconst : (Real.pi / 2) * ABPOnline.cG ^ 2 = 1 := by
      rw [hνsq]
      field_simp
    have hf' := p1Norm_le_cG f hf.1 (isSignFn_abs_le hf)
    have hg' := p1Norm_le_cG g hg.1 (isSignFn_abs_le hg)
    have hnorm : p1Norm f * p1Norm g ≤ ABPOnline.cG ^ 2 := by
      have h1 : p1Norm f * p1Norm g ≤ ABPOnline.cG * p1Norm g :=
        mul_le_mul_of_nonneg_right hf' (Real.sqrt_nonneg _)
      have h2 : ABPOnline.cG * p1Norm g ≤ ABPOnline.cG * ABPOnline.cG :=
        mul_le_mul_of_nonneg_left hg' hν
      nlinarith
    calc
      |(Real.pi / 2) * p1Inner f g| = (Real.pi / 2) * |p1Inner f g| := by
        rw [abs_mul, abs_of_pos (by positivity)]
      _ ≤ (Real.pi / 2) * (p1Norm f * p1Norm g) :=
        mul_le_mul_of_nonneg_left (abs_p1Inner_le f g) (by positivity)
      _ ≤ (Real.pi / 2) * ABPOnline.cG ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = 1 := hconst
