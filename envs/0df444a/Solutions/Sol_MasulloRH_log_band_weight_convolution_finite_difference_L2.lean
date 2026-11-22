-- Prove2me | solution 1 for MasulloRH.log_band_weight_convolution_finite_difference_L2
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:22:53.086177+00:00
-- url     : https://prove2.me/submissions/bd4cfc9b-757e-4a5e-8d2e-f3b9904f4a1b

import Mathlib

/-!
Direct proof of the existing Prove2Me theorem
MasulloRH.log_band_weight_convolution_finite_difference_L2.
No mission definitions, prior submissions, or unproved hypotheses are imported.
-/


/- Source component: LogBandWeightRatioBounds.lean -/
set_option autoImplicit false

namespace MasulloRH.LogBandWeightRatio

noncomputable def polynomialRatio (x y : ℝ) : ℝ :=
  ((1 + x ^ 2) / (1 + (x - y) ^ 2)) ^ 2

theorem polynomialRatio_nonneg (x y : ℝ) : 0 ≤ polynomialRatio x y := by
  exact sq_nonneg _

theorem polynomialRatio_le (R x y : ℝ) (hR : 0 ≤ R) (hy : |y| ≤ R) :
    polynomialRatio x y ≤ 4 * (1 + R ^ 2) ^ 2 := by
  have hd : 0 < 1 + (x-y)^2 := by positivity
  have hyr : y ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hpoly : 1 + x^2 ≤ 2 * (1 + (x-y)^2) * (1 + y^2) := by
    nlinarith [sq_nonneg (x - 2*y),
      mul_nonneg (sq_nonneg (x-y)) (sq_nonneg y)]
  have hr : (1+x^2) / (1+(x-y)^2) ≤ 2*(1+R^2) := by
    apply (div_le_iff₀ hd).2
    calc
      1+x^2 ≤ 2*(1+(x-y)^2)*(1+y^2) := hpoly
      _ ≤ 2*(1+(x-y)^2)*(1+R^2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (2*(1+R^2))*(1+(x-y)^2) := by ring
  have hs := pow_le_pow_left₀
    (by positivity : 0 ≤ (1+x^2)/(1+(x-y)^2)) hr 2
  unfold polynomialRatio
  nlinarith only [hs]

theorem polynomialRatio_sub_one_le (R x y : ℝ) (hR : 0 ≤ R)
    (hy : |y| ≤ R) (hx : 2*R+1 ≤ |x|) :
    |polynomialRatio x y - 1| ≤ 20*(2*R+R^2)/|x| := by
  let d : ℝ := 1+(x-y)^2
  let r : ℝ := (1+x^2)/d
  let K : ℝ := 2*R+R^2
  have hd : 0 < d := by dsimp [d]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hxone : 1 ≤ |x| := by linarith
  have hxpos : 0 < |x| := by linarith
  have ht : |x| ≤ |x-y| + |y| := by
    simpa only [sub_add_cancel, Real.norm_eq_abs] using norm_add_le (x-y) y
  have hhalf : |x|/2 ≤ |x-y| := by linarith
  have hsq : x^2/4 ≤ (x-y)^2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ |x|/2) hhalf 2
    simpa only [div_pow, sq_abs, show (2:ℝ)^2 = 4 by norm_num] using h
  have hden : (1+x^2)/4 ≤ d := by dsimp [d]; linarith
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr4 : r ≤ 4 := by
    dsimp [r]
    exact (div_le_iff₀ hd).2 (by linarith)
  have hyr : y^2 ≤ R^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hnum : |2*x*y-y^2| ≤ K * |x| := by
    calc
      |2*x*y-y^2| ≤ |2*x*y| + |y^2| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (2*x*y) (y^2)
      _ = 2 * |x| * |y| + y^2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2),
          abs_of_nonneg (sq_nonneg y)]
      _ ≤ 2 * |x| * R+R^2 :=
        add_le_add (mul_le_mul_of_nonneg_left hy (by positivity)) hyr
      _ ≤ K * |x| := by
        dsimp [K]
        nlinarith [mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hxone)]
  have heq : r-1 = (2*x*y-y^2)/d := by
    dsimp [r]
    rw [div_sub_one hd.ne']
    congr 1
    dsimp [d]
    ring
  have hdiff : |r-1| ≤ 4*K / |x| := by
    rw [heq, abs_div, abs_of_pos hd]
    apply (div_le_div_iff₀ hd hxpos).2
    calc
      |2*x*y-y^2| * |x| ≤ (K * |x|) * |x| :=
        mul_le_mul_of_nonneg_right hnum (abs_nonneg x)
      _ = K*x^2 := by rw [mul_assoc, ← pow_two, sq_abs]
      _ ≤ (4*K)*d := by
        have hm := mul_le_mul_of_nonneg_left hden hK
        nlinarith only [hm, hK]
  change |r^2-1| ≤ 20*K / |x|
  rw [show r^2-1 = (r-1)*(r+1) by ring, abs_mul,
    abs_of_nonneg (show 0 ≤ r+1 by linarith)]
  calc
    |r-1| * (r+1) ≤ (4*K / |x|)*5 :=
      mul_le_mul hdiff (by linarith) (by linarith) (by positivity)
    _ = 20*K / |x| := by ring


end MasulloRH.LogBandWeightRatio


/- Source component: LogBandConvolutionAnalytic.lean -/
set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Set Filter

noncomputable section

namespace MasulloRH.LogBandConvolution

/-- Reciprocal linear decay on the real line is square integrable. -/
theorem memLp_two_of_norm_le_div_one_add_abs
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C / (1 + |x|)) :
    MemLp f 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm hf).2
  have hdom : Integrable (fun x : ℝ => C ^ 2 * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  apply hdom.mono' (hf.norm.pow 2)
  refine ae_of_all _ fun x => ?_
  change ‖‖f x‖ ^ 2‖ ≤ C ^ 2 * (1 + x ^ 2)⁻¹
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hp : 0 < 1 + |x| := by positivity
  have hq : 0 < 1 + x ^ 2 := by positivity
  have habs : |x| ^ 2 = x ^ 2 := sq_abs x
  have hs : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x]
  calc
    ‖f x‖ ^ 2 ≤ (C / (1 + |x|)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2
    _ = C ^ 2 / (1 + |x|) ^ 2 := div_pow _ _ _
    _ ≤ C ^ 2 / (1 + x ^ 2) := div_le_div_of_nonneg_left (sq_nonneg _) hq hs
    _ = C ^ 2 * (1 + x ^ 2)⁻¹ := div_eq_mul_inv _ _

def twoSidedStep (cplus cminus : ℂ) (x : ℝ) : ℂ :=
  if 0 ≤ x then cplus else cminus

theorem measurable_twoSidedStep (cplus cminus : ℂ) :
    Measurable (twoSidedStep cplus cminus) := by
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

theorem norm_twoSidedStep_le (cplus cminus : ℂ) (x : ℝ) :
    ‖twoSidedStep cplus cminus x‖ ≤ ‖cplus‖ + ‖cminus‖ := by
  unfold twoSidedStep
  split_ifs <;> linarith [norm_nonneg cplus, norm_nonneg cminus]

/-- Translating a function constant on either half-line changes it only on a compact interval. -/
theorem memLp_twoSidedStep_difference (cplus cminus : ℂ) (d : ℝ) :
    MemLp (fun x => twoSidedStep cplus cminus (x + d) -
      twoSidedStep cplus cminus x) 2 volume := by
  have hcompact : HasCompactSupport (fun x =>
      twoSidedStep cplus cminus (x + d) - twoSidedStep cplus cminus x) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := -|d|) (b := |d|))
    intro x hx
    have hx' : x < -|d| ∨ |d| < x := by
      simpa only [mem_Icc, not_and_or, not_le] using hx
    rcases hx' with hx' | hx'
    · have hx0 : ¬0 ≤ x := by linarith [abs_nonneg d]
      have hxd0 : ¬0 ≤ x + d := by linarith [le_abs_self d]
      simp [twoSidedStep, hx0, hxd0]
    · have hx0 : 0 ≤ x := by linarith [abs_nonneg d]
      have hxd0 : 0 ≤ x + d := by linarith [neg_abs_le d]
      simp [twoSidedStep, hx0, hxd0]
  have hm : Measurable (fun x => twoSidedStep cplus cminus (x + d) -
      twoSidedStep cplus cminus x) :=
    ((measurable_twoSidedStep cplus cminus).comp
      (measurable_id.add measurable_const)).sub (measurable_twoSidedStep cplus cminus)
  apply hcompact.memLp_of_bound hm.aestronglyMeasurable (2 * (‖cplus‖ + ‖cminus‖))
  refine ae_of_all _ fun x => ?_
  calc
    _ ≤ ‖twoSidedStep cplus cminus (x + d)‖ + ‖twoSidedStep cplus cminus x‖ :=
      norm_sub_le _ _
    _ ≤ (‖cplus‖ + ‖cminus‖) + (‖cplus‖ + ‖cminus‖) :=
      add_le_add (norm_twoSidedStep_le _ _ _) (norm_twoSidedStep_le _ _ _)
    _ = _ := by ring

/-- An L² error relative to two constants at the two ends has L² finite differences. -/
theorem memLp_difference_of_twoSidedStep_remainder
    (b : ℝ → ℂ) (cplus cminus : ℂ)
    (hr : MemLp (fun x => b x - twoSidedStep cplus cminus x) 2 volume)
    (d : ℝ) : MemLp (fun x => b (x + d) - b x) 2 volume := by
  have hshift := hr.comp_measurePreserving (measurePreserving_add_right volume d)
  have h := (hshift.sub hr).add (memLp_twoSidedStep_difference cplus cminus d)
  convert h using 1
  funext x
  change b (x+d) - b x =
    ((b (x+d) - twoSidedStep cplus cminus (x+d)) -
      (b x - twoSidedStep cplus cminus x)) +
        (twoSidedStep cplus cminus (x+d) - twoSidedStep cplus cminus x)
  abel

/-- A bounded continuous function with reciprocal-linear errors at both ends has L² differences. -/
theorem memLp_difference_of_two_sided_tail
    (b : ℝ → ℂ) (hb : Continuous b)
    (M : ℝ) (hM : 0 ≤ M) (hbounded : ∀ x, ‖b x‖ ≤ M)
    (cplus cminus : ℂ) (R C : ℝ) (hR : 1 ≤ R) (hC : 0 ≤ C)
    (htail : ∀ x, R ≤ |x| →
      ‖b x - twoSidedStep cplus cminus x‖ ≤ C / |x|)
    (d : ℝ) : MemLp (fun x => b (x + d) - b x) 2 volume := by
  apply memLp_difference_of_twoSidedStep_remainder b cplus cminus _ d
  let B := M + ‖cplus‖ + ‖cminus‖
  let K := 2 * C + B * (1 + R)
  have hR0 : 0 ≤ R := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply memLp_two_of_norm_le_div_one_add_abs _
    (hb.aestronglyMeasurable.sub
      (measurable_twoSidedStep cplus cminus).aestronglyMeasurable) K hK
  intro x
  have hp : 0 < 1 + |x| := by positivity
  by_cases hx : R ≤ |x|
  · have hxpos : 0 < |x| := lt_of_lt_of_le (by linarith) hx
    have h1 : 1 ≤ |x| := hR.trans hx
    have hCK : 2 * C ≤ K := by
      dsimp [K]
      exact le_add_of_nonneg_right (mul_nonneg hB (by positivity))
    calc
      _ ≤ C / |x| := htail x hx
      _ ≤ (2 * C) / (1 + |x|) := by
        apply (div_le_div_iff₀ hxpos hp).2
        nlinarith [mul_nonneg hC (sub_nonneg.mpr h1)]
      _ ≤ K / (1 + |x|) := div_le_div_of_nonneg_right hCK hp.le
  · have hxR : |x| ≤ R := (lt_of_not_ge hx).le
    have hbase : ‖b x - twoSidedStep cplus cminus x‖ ≤ B := by
      calc
        _ ≤ ‖b x‖ + ‖twoSidedStep cplus cminus x‖ := norm_sub_le _ _
        _ ≤ M + (‖cplus‖ + ‖cminus‖) :=
          add_le_add (hbounded x) (norm_twoSidedStep_le _ _ _)
        _ = B := by dsimp [B]; ring
    apply hbase.trans
    apply (le_div_iff₀ hp).2
    dsimp [K]
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hxR)]

/-- Positivity and continuity of the weight suffice for continuity of the weighted convolution. -/
theorem continuous_weighted_compact_convolution
    (w : ℝ → ℝ) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (h : ℝ → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h) :
    Continuous (fun x => (w x : ℂ) * ∫ y : ℝ, h y / (w (x-y) : ℂ)) := by
  apply (Complex.continuous_ofReal.comp hw).mul
  rw [← continuousOn_univ]
  have hkernel : Continuous (fun z : ℝ × ℝ => h z.2 / (w (z.1-z.2) : ℂ)) := by
    apply (hh.comp continuous_snd).div
      (Complex.continuous_ofReal.comp (hw.comp (continuous_fst.sub continuous_snd)))
    intro z
    change (w (z.1-z.2) : ℂ) ≠ 0
    exact_mod_cast (hwpos (z.1-z.2)).ne'
  apply continuousOn_integral_of_compact_support hhc hkernel.continuousOn
  intro x y _ hy
  rw [image_eq_zero_of_notMem_tsupport hy, zero_div]

theorem weighted_convolution_eq_integral (w : ℝ → ℝ) (h : ℝ → ℂ) (x : ℝ) :
    (w x : ℂ) * (∫ y : ℝ, h y / (w (x-y) : ℂ)) =
      ∫ y : ℝ, h y * ((w x / w (x-y) : ℝ) : ℂ) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ fun y => ?_
  simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- A uniform ratio bound on the support of the compact input controls the convolution globally. -/
theorem weighted_compact_convolution_bound
    (w : ℝ → ℝ) (hwpos : ∀ x, 0 < w x)
    (h : ℝ → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h)
    (B : ℝ) (hB : 0 ≤ B)
    (hratio : ∀ x y, y ∈ tsupport h → w x / w (x-y) ≤ B) (x : ℝ) :
    ‖(w x : ℂ) * (∫ y : ℝ, h y / (w (x-y) : ℂ))‖ ≤
      B * ∫ y : ℝ, ‖h y‖ := by
  rw [weighted_convolution_eq_integral]
  calc
    _ ≤ ∫ y : ℝ, B * ‖h y‖ := by
      apply norm_integral_le_of_norm_le ((hh.integrable_of_hasCompactSupport hhc).norm.const_mul B)
      refine ae_of_all _ fun y => ?_
      by_cases hy : y ∈ tsupport h
      · rw [norm_mul, Complex.norm_of_nonneg (div_nonneg (hwpos x).le (hwpos (x-y)).le)]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (hratio x y hy) (norm_nonneg (h y))
      · simp [image_eq_zero_of_notMem_tsupport hy]
    _ = _ := integral_const_mul _ _

/-- Uniform kernel error on the support of a compact input bounds the error of its integral. -/
theorem integral_mul_error_bound
    (h : ℝ → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h)
    (a e : ℝ → ℝ) (ha : Continuous a) (he : Continuous e)
    (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ y, y ∈ tsupport h → |a y - e y| ≤ D) :
    ‖(∫ y : ℝ, h y * (a y : ℂ)) - (∫ y : ℝ, h y * (e y : ℂ))‖ ≤
      D * ∫ y : ℝ, ‖h y‖ := by
  have hai : Integrable (fun y => h y * (a y : ℂ)) :=
    (hh.mul (Complex.continuous_ofReal.comp ha)).integrable_of_hasCompactSupport hhc.mul_right
  have hei : Integrable (fun y => h y * (e y : ℂ)) :=
    (hh.mul (Complex.continuous_ofReal.comp he)).integrable_of_hasCompactSupport hhc.mul_right
  rw [← integral_sub hai hei]
  calc
    _ ≤ ∫ y : ℝ, D * ‖h y‖ := by
      apply norm_integral_le_of_norm_le ((hh.integrable_of_hasCompactSupport hhc).norm.const_mul D)
      refine ae_of_all _ fun y => ?_
      by_cases hy : y ∈ tsupport h
      · rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (hbound y hy) (norm_nonneg (h y))
      · simp [image_eq_zero_of_notMem_tsupport hy]
    _ = _ := integral_const_mul _ _

/-- Two-sided asymptotics of weight ratios imply boundedness and L² translation differences. -/
theorem weighted_convolution_finite_difference_of_ratio_asymptotics
    (w : ℝ → ℝ) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (h : ℝ → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h)
    (B : ℝ) (hB : 0 ≤ B)
    (hratio : ∀ x y, y ∈ tsupport h → w x / w (x-y) ≤ B)
    (aplus aminus : ℝ → ℝ) (haplus : Continuous aplus) (haminus : Continuous aminus)
    (R C : ℝ) (hR : 1 ≤ R) (hC : 0 ≤ C)
    (htail : ∀ x, R ≤ |x| → ∀ y, y ∈ tsupport h →
      |w x / w (x-y) - (if 0 ≤ x then aplus y else aminus y)| ≤ C / |x|) :
    let b : ℝ → ℂ := fun x => (w x : ℂ) * ∫ y : ℝ, h y / (w (x-y) : ℂ)
    Continuous b ∧ (∃ M : ℝ, ∀ x, ‖b x‖ ≤ M) ∧
      ∀ d : ℝ, MemLp (fun x => b (x+d) - b x) 2 volume := by
  dsimp only
  let b : ℝ → ℂ := fun x => (w x : ℂ) * ∫ y : ℝ, h y / (w (x-y) : ℂ)
  let H : ℝ := ∫ y : ℝ, ‖h y‖
  have hH : 0 ≤ H := integral_nonneg fun y => norm_nonneg (h y)
  have hcont := continuous_weighted_compact_convolution w hw hwpos h hh hhc
  have hbounded := weighted_compact_convolution_bound w hwpos h hh hhc B hB hratio
  refine ⟨hcont, ⟨B * H, hbounded⟩, ?_⟩
  intro d
  apply memLp_difference_of_two_sided_tail b hcont (B * H) (mul_nonneg hB hH) hbounded
    (∫ y : ℝ, h y * (aplus y : ℂ)) (∫ y : ℝ, h y * (aminus y : ℂ))
    R (C * H) hR (mul_nonneg hC hH) _ d
  intro x hx
  have ha : Continuous (fun y : ℝ => w x / w (x-y)) :=
    continuous_const.div (hw.comp (continuous_const.sub continuous_id))
      (fun y => (hwpos (x-y)).ne')
  have hD : 0 ≤ C / |x| := div_nonneg hC (abs_nonneg x)
  dsimp only [b]
  rw [weighted_convolution_eq_integral]
  by_cases hx0 : 0 ≤ x
  · simp only [twoSidedStep, hx0, if_true]
    have he := integral_mul_error_bound h hh hhc
      (fun y => w x / w (x-y)) aplus ha haplus (C / |x|) hD
      (fun y hy => by simpa only [hx0, if_true] using htail x hx y hy)
    convert he using 1 <;> dsimp only [H] <;> ring
  · simp only [twoSidedStep, hx0, if_false]
    have he := integral_mul_error_bound h hh hhc
      (fun y => w x / w (x-y)) aminus ha haminus (C / |x|) hD
      (fun y hy => by simpa only [hx0, if_false] using htail x hx y hy)
    convert he using 1 <;> dsimp only [H] <;> ring

end MasulloRH.LogBandConvolution


/- Source component: LogBandConvolution.lean -/
set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Set

namespace MasulloRH.LogBandConvolution

noncomputable def weight (α x : ℝ) : ℝ :=
  Real.exp (2 * α * |x|) * (1 + x ^ 2) ^ 2

theorem weight_pos (α x : ℝ) : 0 < weight α x := by
  unfold weight
  positivity

theorem continuous_weight (α : ℝ) : Continuous (weight α) := by
  unfold weight
  fun_prop

theorem weight_ratio (α x y : ℝ) :
    weight α x / weight α (x-y) =
      Real.exp (2 * α * (|x| - |x-y|)) *
        LogBandWeightRatio.polynomialRatio x y := by
  unfold weight LogBandWeightRatio.polynomialRatio
  rw [mul_div_mul_comm, ← div_pow, ← Real.exp_sub]
  congr 2
  ring

theorem weight_ratio_le (α R x y : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R) (hy : |y| ≤ R) :
    weight α x / weight α (x-y) ≤
      Real.exp (2 * α * R) * (4 * (1 + R ^ 2) ^ 2) := by
  rw [weight_ratio]
  have habs : |x| - |x-y| ≤ R := by
    have ht := abs_add_le (x-y) y
    rw [sub_add_cancel] at ht
    linarith
  apply mul_le_mul
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs (by positivity)))
    (LogBandWeightRatio.polynomialRatio_le R x y hR hy)
    (LogBandWeightRatio.polynomialRatio_nonneg x y) (Real.exp_nonneg _)

theorem weight_ratio_tail_error (α R x y : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R)
    (hy : |y| ≤ R) (hx : 2 * R + 1 ≤ |x|) :
    |weight α x / weight α (x-y) -
      (if 0 ≤ x then Real.exp (2 * α * y) else Real.exp (-2 * α * y))| ≤
      (Real.exp (2 * α * R) * (20 * (2 * R + R ^ 2))) / |x| := by
  let a : ℝ := if 0 ≤ x then Real.exp (2 * α * y) else Real.exp (-2 * α * y)
  have ha : 0 ≤ a := by dsimp [a]; split_ifs <;> positivity
  have hylo : -R ≤ y := by linarith [neg_abs_le y]
  have hyhi : y ≤ R := (le_abs_self y).trans hy
  have ha_le : a ≤ Real.exp (2 * α * R) := by
    dsimp [a]
    split_ifs
    · apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hyhi (by positivity)
    · apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hylo (show 0 ≤ 2 * α by positivity)
      nlinarith only [hm]
  have hratio : weight α x / weight α (x-y) =
      a * LogBandWeightRatio.polynomialRatio x y := by
    rw [weight_ratio]
    dsimp [a]
    by_cases hx0 : 0 ≤ x
    · have hx' : 2 * R + 1 ≤ x := by simpa only [abs_of_nonneg hx0] using hx
      have hxy : 0 ≤ x-y := by linarith
      simp only [hx0, if_true, abs_of_nonneg hx0, abs_of_nonneg hxy]
      congr 2
      ring
    · have hx0' : x ≤ 0 := (lt_of_not_ge hx0).le
      have hx' : 2 * R + 1 ≤ -x := by simpa only [abs_of_nonpos hx0'] using hx
      have hxy : x-y ≤ 0 := by linarith
      simp only [hx0, if_false, abs_of_nonpos hx0', abs_of_nonpos hxy]
      congr 2
      ring
  change |weight α x / weight α (x-y) - a| ≤ _
  rw [hratio, show a * LogBandWeightRatio.polynomialRatio x y - a =
    a * (LogBandWeightRatio.polynomialRatio x y - 1) by ring,
    abs_mul, abs_of_nonneg ha]
  calc
    _ ≤ Real.exp (2 * α * R) * (20 * (2 * R + R ^ 2) / |x|) :=
      mul_le_mul ha_le
        (LogBandWeightRatio.polynomialRatio_sub_one_le R x y hR hy hx)
        (abs_nonneg _) (Real.exp_nonneg _)
    _ = _ := by ring

end MasulloRH.LogBandConvolution

namespace MasulloRH

theorem log_band_weight_convolution_finite_difference_L2
    (α : ℝ) (hα : 0 ≤ α) (h : ℝ → ℂ)
    (hh : Continuous h) (hhc : HasCompactSupport h) :
    let w : ℝ → ℝ := fun x : ℝ => Real.exp (2 * α * |x|) * (1 + x^2)^2
    let b : ℝ → ℂ := fun x : ℝ => (w x : ℂ) * ∫ y : ℝ, h y / (w (x-y) : ℂ)
    Continuous b ∧ (∃ M : ℝ, ∀ x : ℝ, ‖b x‖ ≤ M) ∧
      ∀ d : ℝ, MemLp (fun x => b (x+d) - b x) 2 volume := by
  obtain ⟨R, hRpos, hsupp⟩ := hhc.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  have hR : 0 ≤ R := hRpos.le
  have hsupport : ∀ y, y ∈ tsupport h → |y| ≤ R := by
    intro y hy
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hsupp hy
  exact LogBandConvolution.weighted_convolution_finite_difference_of_ratio_asymptotics
    (LogBandConvolution.weight α) (LogBandConvolution.continuous_weight α)
    (LogBandConvolution.weight_pos α) h hh hhc
    (Real.exp (2 * α * R) * (4 * (1 + R ^ 2) ^ 2)) (by positivity)
    (fun x y hy => LogBandConvolution.weight_ratio_le α R x y hα hR (hsupport y hy))
    (fun y => Real.exp (2 * α * y)) (fun y => Real.exp (-2 * α * y))
    (by fun_prop) (by fun_prop)
    (2 * R + 1) (Real.exp (2 * α * R) * (20 * (2 * R + R ^ 2)))
    (by linarith) (by positivity)
    (fun x hx y hy =>
      LogBandConvolution.weight_ratio_tail_error α R x y hα hR (hsupport y hy) hx)

end MasulloRH



/- Submission-protocol entry point, with the existing target statement unchanged. -/
theorem solution (α : ℝ) (hα : 0 ≤ α) (h : ℝ → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h) :
    let w : ℝ → ℝ := fun x : ℝ => Real.exp (2 * α * |x|) * (1 + x^2)^2
    let b : ℝ → ℂ := fun x : ℝ => (w x : ℂ) * ∫ y : ℝ, h y / (w (x-y) : ℂ)
    Continuous b ∧ (∃ M : ℝ, ∀ x : ℝ, ‖b x‖ ≤ M) ∧ ∀ d : ℝ, MemLp (fun x => b (x+d) - b x) 2 volume := by
  exact MasulloRH.log_band_weight_convolution_finite_difference_L2 α hα h hh hhc

#print axioms solution
