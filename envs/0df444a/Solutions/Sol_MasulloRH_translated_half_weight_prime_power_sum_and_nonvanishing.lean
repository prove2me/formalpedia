-- Prove2me | solution 1 for MasulloRH.translated_half_weight_prime_power_sum_and_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:55:34.922607+00:00
-- url     : https://prove2.me/submissions/f98573ca-9576-43a8-9337-0092c18227df

import Theorems.Thm_ZetaNine_HarmonicStability_psi_pnt_rate
import Theorems.Thm_MasulloRH_exists_positive_log_profile_rank_discriminator
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter MeasureTheory Set
open scoped Topology ArithmeticFunction

private theorem masullo_psi_uniform_rescale
    (hpnt : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn (fun X t : ℝ => Chebyshev.psi (X*t)/X) id atTop (Icc a b) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨D,hD⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hpnt (ε/b) (div_pos hε hb))
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_ge_atTop (D/a)] with X hX hXa
  intro t ht
  have ht0 := ha.trans_le ht.1
  have hD' : D ≤ X*t := ((div_le_iff₀ ha).mp hXa).trans (mul_le_mul_of_nonneg_left ht.1 hX.le)
  have h := hD (X*t) hD'
  rw [Real.dist_eq] at h
  have he : t - Chebyshev.psi (X*t)/X = -(Chebyshev.psi (X*t)/(X*t)-1)*t := by
    field_simp [hX.ne',ht0.ne']
    ring
  rw [Real.dist_eq, id_eq, he, abs_mul, abs_neg, abs_of_nonneg ht0.le]
  calc
    _ ≤ |Chebyshev.psi (X*t)/(X*t)-1| * b := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)
    _ < _ := (lt_div_iff₀ hb).mp h

private theorem masullo_psi_integral_rescale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hpnt : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (h : ℝ → E) (hh : IntegrableOn h (Icc a b)) :
    Tendsto (fun X : ℝ => ∫ t in Icc a b, (Chebyshev.psi (X*t)/X) • h t)
      atTop (𝓝 (∫ t in Icc a b, t • h t)) := by
  have hu := masullo_psi_uniform_rescale hpnt ha hab
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hm : ∀ᵐ t ∂μ, t ∈ Icc a b := ae_restrict_mem measurableSet_Icc
  apply tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (fun t => (b+1)*‖h t‖) _ _ (hh.norm.const_mul _) _
  · apply Eventually.of_forall
    intro X
    have hψ : Measurable (fun t : ℝ => Chebyshev.psi (X*t)/X) :=
      (Chebyshev.psi_mono.measurable.comp (measurable_const.mul measurable_id)).div_const _
    exact hψ.aestronglyMeasurable.smul hh.aestronglyMeasurable
  · filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one] with X hX
    filter_upwards [hm] with t ht
    have he := hX t ht
    simp only [Real.dist_eq, id_eq] at he
    have hpos := ha.trans_le ht.1
    have hnorm : ‖Chebyshev.psi (X*t)/X‖ ≤ b+1 := by
      rw [Real.norm_eq_abs, abs_le]
      obtain ⟨hl,hr⟩ := abs_lt.mp he
      constructor <;> linarith [ht.2]
    exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  · filter_upwards [hm] with t ht
    exact (hu.tendsto_at ht).smul (tendsto_const_nhds (x := h t))

private theorem c11_abel_rescale {a b X : ℝ} (ha : 0 < a) (hab : a ≤ b) (hX : 0 < X)
    (g gp : ℝ → ℝ) (hd : ∀ t ∈ Set.Icc a b, HasDerivAt g (gp t) t)
    (hgp : ContinuousOn gp (Set.Icc a b)) (hga : g a = 0) (hgb : g b = 0) :
    (∑ n ∈ Finset.Ioc ⌊a*X⌋₊ ⌊b*X⌋₊, g ((n:ℝ)/X) * ArithmeticFunction.vonMangoldt n) / X =
      -(∫ t in a..b, (Chebyshev.psi (X*t)/X) * gp t) := by
  let G (x : ℝ) := g (x/X)
  have hmap {x : ℝ} (hx : x ∈ Set.Icc (a*X) (b*X)) : x/X ∈ Set.Icc a b :=
    ⟨(le_div_iff₀ hX).2 hx.1, (div_le_iff₀ hX).2 hx.2⟩
  have hdG {x : ℝ} (hx : x ∈ Set.Icc (a*X) (b*X)) :
      HasDerivAt G (gp (x/X) / X) x := by
    simpa [G, Function.comp_def,div_eq_mul_inv] using
      (hd _ (hmap hx)).comp x ((hasDerivAt_id x).div_const X)
  have hc : ContinuousOn (deriv G) (Set.Icc (a*X) (b*X)) := by
    apply ((hgp.comp (continuous_id.div_const X).continuousOn (fun x hx => hmap hx)).div_const X).congr
    intro x hx
    exact (hdG hx).deriv
  have habX : a * X ≤ b * X := mul_le_mul_of_nonneg_right hab hX.le
  have H := sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt (f := G)
    (mul_nonneg ha.le hX.le) habX (fun x hx => (hdG hx).differentiableAt) hc.integrableOn_Icc
  change (∑ n ∈ Finset.Ioc ⌊a*X⌋₊ ⌊b*X⌋₊, G ↑n * ArithmeticFunction.vonMangoldt n) / X = _
  rw [H]
  have G1 : G (a*X) = 0 := by simpa [G, hX.ne'] using hga
  have G2 : G (b*X) = 0 := by simpa [G, hX.ne'] using hgb
  rw [G1,G2,zero_mul,zero_mul,sub_zero,zero_sub,neg_div,neg_inj]
  simp_rw [← Chebyshev.psi_eq_sum_Icc]
  rw [← intervalIntegral.integral_of_le habX]
  let F (x : ℝ) := deriv G x * Chebyshev.psi x
  change (∫ x in a*X..b*X, F x) / X = _
  have hsub := intervalIntegral.integral_comp_mul_right (a := a) (b := b) F hX.ne'
  rw [smul_eq_mul, ← div_eq_inv_mul] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have htX : t*X ∈ Set.Icc (a*X) (b*X) := ⟨by gcongr; exact ht.1, by gcongr; exact ht.2⟩
  dsimp [F]
  rw [(hdG htX).deriv, mul_div_cancel_right₀ t hX.ne', mul_comm X t]
  ring

private theorem c11_weighted_prime_limit
    (hpnt : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hfa : f a = 0) (hfb : f b = 0) :
    Tendsto (fun X : ℝ =>
        (∑ n ∈ Finset.Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n * f ((n:ℝ)/X)) / Real.sqrt X)
      atTop (𝓝 (∫ t in a..b, f t / Real.sqrt t)) := by
  let g (t : ℝ) := f t / Real.sqrt t
  let gp (t : ℝ) := (deriv f t * Real.sqrt t - f t * (2*Real.sqrt t)⁻¹) / (Real.sqrt t)^2
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt g (gp t) t := by
    have htpos : 0 < t := ha.trans_le ht.1
    change HasDerivAt (f / fun t : ℝ => Real.sqrt t) _ t
    simpa [gp, one_div] using ((hf.differentiable (by simp)).differentiableAt.hasDerivAt.div
      (Real.hasDerivAt_sqrt htpos.ne') (Real.sqrt_pos.mpr htpos).ne')
  have hgp : ContinuousOn gp (Set.Icc a b) := by
    intro t ht
    have htpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr (ha.trans_le ht.1)
    have hd' : ContinuousAt (deriv f) t := (hf.continuous_deriv le_rfl).continuousAt
    have hs := Real.continuous_sqrt.continuousAt (x := t)
    exact (((hd'.mul hs).sub (hf.continuous.continuousAt.mul
      ((continuousAt_const.mul hs).inv₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) htpos.ne')))).div (hs.pow 2) (pow_ne_zero 2 htpos.ne')).continuousWithinAt
  have hga : g a = 0 := by simp [g,hfa]
  have hgb : g b = 0 := by simp [g,hfb]
  have hih : IntervalIntegrable gp volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hgp.integrableOn_Icc
  have ih := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := id) (u' := fun _ : ℝ => 1) (v := g) (v' := gp)
      (fun t _ => hasDerivAt_id t)
      (fun t ht => hd t (by simpa [Set.uIcc_of_le hab] using ht)) (by simp) hih
  have hcalc : -(∫ t in a..b, t * gp t) = ∫ t in a..b, g t := by simpa [hga,hgb] using congrArg Neg.neg ih
  have hconv := masullo_psi_integral_rescale hpnt ha hab gp hgp.integrableOn_Icc
  have hconv' : Tendsto (fun X : ℝ => -(∫ t in a..b, (Chebyshev.psi (X*t)/X) * gp t)) atTop
        (𝓝 (∫ t in a..b, g t)) := by
    rw [← hcalc]
    simpa only [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc, smul_eq_mul]
      using hconv.neg
  apply hconv'.congr' _
  filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
  rw [← c11_abel_rescale ha hab hX g gp hd hgp hga hgb]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  dsimp [g]
  rw [Real.sqrt_div (by positivity)]
  have hs := Real.sq_sqrt hX.le
  by_cases hn : (n:ℝ) = 0
  · simp [hn]
  have hn' : Real.sqrt (n:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn)))
  have hX' := (Real.sqrt_pos.mpr hX).ne'
  field_simp
  linear_combination (f (↑n / X) * ArithmeticFunction.vonMangoldt n) * hs

private theorem c11_half_mellin {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : tsupport f ⊆ Set.Ioo a b) :
    (mellin (fun t => (f t : ℂ)) (1/2 : ℂ)).re = ∫ t in a..b, f t / Real.sqrt t := by
  have hsub : Set.Ioc a b ⊆ Set.Ioi (0:ℝ) := fun t ht => ha.trans ht.1
  have hh : ∀ t ∉ Set.Ioc a b, f t = 0 := by
    intro t ht
    exact image_eq_zero_of_notMem_tsupport (fun h => ht ⟨(hf h).1,(hf h).2.le⟩)
  have heq : Set.EqOn (fun t : ℝ => (t:ℂ)^((1/2:ℂ)-1) • (f t:ℂ))
      (fun t => ((f t / Real.sqrt t : ℝ) : ℂ)) (Set.Ioi 0) := by
    intro t ht
    change (t : ℂ) ^ ((1/2:ℂ)-1) * (f t:ℂ) = _
    rw [show (1/2:ℂ)-1 = ((-(1/2):ℝ):ℂ) by norm_num, ← Complex.ofReal_cpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht), ← Real.sqrt_eq_rpow]
    push_cast
    ring
  have hi : (∫ t in Set.Ioi (0:ℝ), ((f t / Real.sqrt t : ℝ) : ℂ)) =
      ((∫ t in Set.Ioi (0:ℝ), f t / Real.sqrt t : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Set.Ioi (0:ℝ))) (f := fun t => f t / Real.sqrt t)
  rw [mellin,setIntegral_congr_fun measurableSet_Ioi heq, hi, Complex.ofReal_re]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub (fun t ht => by simp [hh t ht.2]),
      intervalIntegral.integral_of_le hab]


theorem solution :
    (∀ (a b : ℝ), 0 < a → a ≤ b → ∀ f : ℝ → ℝ, ContDiff ℝ 1 f →
      tsupport f ⊆ Set.Ioo a b →
      Tendsto (fun X : ℝ =>
        (∑ n ∈ Finset.Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n * f ((n:ℝ)/X)) / Real.sqrt X)
        atTop (𝓝 ((mellin (fun t => (f t : ℂ)) (1/2 : ℂ)).re))) ∧
    (∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Set.Ioo 1 32 ∧
      HasMellin (fun t => (f t : ℂ)) 1 0 ∧ HasMellin (fun t => (f t : ℂ)) (-(1/2) : ℂ) 0 ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
        c * Real.sqrt X ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊32*X⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n * f ((n:ℝ)/X)) := by
  have H (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
      (hs : tsupport f ⊆ Set.Ioo a b) := by
    have hfa : f a = 0 := image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl a) (hs h).1)
    have hfb : f b = 0 := image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl b) (hs h).2)
    have h := c11_weighted_prime_limit ZetaNine.HarmonicStability.psi_pnt_rate a b ha hab f hf hfa hfb
    rw [← c11_half_mellin ha hab f hs] at h
    exact h
  refine ⟨H, ?_⟩
  obtain ⟨f,hf,hc,hs,h1,hm,hp,_⟩ := MasulloRH.exists_positive_log_profile_rank_discriminator
  let m := (mellin (fun t => (f t : ℂ)) (1/2:ℂ)).re
  refine ⟨f,hf,hc,hs,h1,hm,m/2,half_pos hp,?_⟩
  have Hf := H 1 32 zero_lt_one (by norm_num) f (hf.of_le (by exact_mod_cast (le_top : (1:ℕ∞) ≤ ⊤))) hs
  have hpos : m/2 < m := half_lt_self hp
  filter_upwards [Hf.eventually_const_lt hpos, eventually_gt_atTop (0:ℝ)] with X hx hX
  simpa only [one_mul] using ((lt_div_iff₀ (Real.sqrt_pos.mpr hX)).mp hx).le
