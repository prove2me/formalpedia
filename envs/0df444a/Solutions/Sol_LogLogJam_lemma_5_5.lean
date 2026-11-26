-- Prove2me | solution 1 for LogLogJam.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:19:50.421949+00:00
-- url     : https://prove2.me/submissions/3966a6f3-d860-46aa-92d9-fe7e24ed2e26

import Mathlib
import Definitions.Def_LogLogJam_fisherInfo

open MeasureTheory Filter LogLogJam
open scoped ENNReal Topology

private theorem sigmaPositive {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℝ) (hp : ∀ x, 0 < u x) (hm : Measurable u)
    (hn : ∫⁻ x, ENNReal.ofReal (u x) ∂μ = 1) : SigmaFinite μ := by
  let r (n : ℕ) := ENNReal.ofReal (1 / (n + 1 : ℝ))
  have hr n : r n ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  refine ⟨⟨⟨(fun n => {x | r n ≤ ENNReal.ofReal (u x)}), fun _ => Set.mem_univ _, ?_, ?_⟩⟩⟩
  · intro n
    have h := meas_ge_le_lintegral_div (μ := μ) hm.ennreal_ofReal.aemeasurable (hr n) ENNReal.ofReal_ne_top
    rw [hn] at h
    exact h.trans_lt (ENNReal.div_lt_top (by simp) (hr n))
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hp x)
    exact Set.mem_iUnion.mpr ⟨n, ENNReal.ofReal_le_ofReal hn.le⟩

private theorem derivMeasurable {X : Type*} [MeasurableSpace X] (q : ℝ → X → ℝ)
    (hC : ∀ x, ContDiff ℝ 1 (fun t => q t x)) (hm : ∀ t, Measurable (q t)) :
    Measurable (fun z : ℝ × X => deriv (fun t => q t z.2) z.1) := by
  apply measurable_uncurry_of_continuous_of_measurable (fun x => (hC x).continuous_deriv_one)
  intro t
  let d (n : ℕ) : ℝ := 1 / (n+1 : ℝ)
  have hlim : Tendsto d atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall fun n => by change 0 < 1 / (n+1 : ℝ); positivity⟩
  apply measurable_of_tendsto_metrizable (f := fun (n : ℕ) x => (d n)⁻¹ * (q (t+d n) x - q t x))
    (fun n => measurable_const.mul ((hm _).sub (hm _)))
  apply tendsto_pi_nhds.mpr
  intro x
  exact ((hC x).differentiable_one t).hasDerivAt.tendsto_slope_zero_right.comp hlim

private theorem anchored {f : ℝ → ℝ} (hc : ContDiff ℝ 1 f) (hp : Function.Periodic f Real.pi)
    (h0 : 0 ≤ f 0) (t : ℝ) :
    ENNReal.ofReal (f t) ≤ ENNReal.ofReal (f 0) + ∫⁻ s in Set.Ico 0 Real.pi, ENNReal.ofReal |deriv f s| := by
  let x := toIcoMod Real.pi_pos 0 t
  have hx := toIcoMod_mem_Ico' Real.pi_pos t
  have he : f x = f t := hp.sub_zsmul_eq _
  have hd := hc.continuous_deriv_one
  have hFt := intervalIntegral.integral_deriv_eq_sub (a := 0) (b := x)
    (fun s _ => hc.differentiable_one s) (hd.intervalIntegrable _ _)
  have hosc := (intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := deriv f) hx.1).trans
    (intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2.le
      (Eventually.of_forall fun s => abs_nonneg _) (hd.abs.intervalIntegrable _ _))
  change |∫ y in (0 : ℝ)..x, deriv f y| ≤ _ at hosc
  rw [hFt, he] at hosc
  have hsi : f t ≤ f 0 + ∫ y in (0 : ℝ)..Real.pi, |deriv f y| := by linarith [le_abs_self (f t-f 0)]
  apply (ENNReal.ofReal_le_ofReal hsi).trans_eq
  rw [ENNReal.ofReal_add h0 (intervalIntegral.integral_nonneg Real.pi_pos.le (fun _ _ => abs_nonneg _)),
    intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_Ico_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal (hd.abs.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
      (Eventually.of_forall fun _ => abs_nonneg _)]

private theorem normalizeRoot (F : ℝ≥0∞) :
    ENNReal.ofReal Real.pi ^ (1/2 : ℝ) * F ^ (1/2 : ℝ) = ENNReal.ofReal Real.pi *
      (ENNReal.ofReal (1/Real.pi) * F) ^ (1/2 : ℝ) := by
  let c := ENNReal.ofReal Real.pi
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr Real.pi_pos).ne'
  have hcT : c ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [one_div Real.pi, ENNReal.ofReal_inv_of_pos Real.pi_pos, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.inv_rpow, ← ENNReal.rpow_neg, ← mul_assoc]
  change c ^ (1/2 : ℝ) * _ = (c * c ^ (-(1/2) : ℝ)) * _
  have he : c * c ^ (-(1/2) : ℝ) = c ^ (1/2 : ℝ) := by
    calc
      _ = c ^ (1 : ℝ) * c ^ (-(1/2) : ℝ) := by rw [ENNReal.rpow_one]
      _ = _ := by rw [← ENNReal.rpow_add _ _ hc0 hcT]; norm_num
  rw [he]

theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (q : ℝ → X → ℝ)
    (hpos : ∀ θ x, 0 < q θ x) (hper : ∀ θ x, q (θ + Real.pi) x = q θ x)
    (hC1 : ∀ x, ContDiff ℝ 1 (fun θ => q θ x)) (hmeas : ∀ θ, Measurable (q θ))
    (hnorm : ∀ θ, ∫⁻ x, ENNReal.ofReal (q θ x) ∂μ = 1) :
    ∫⁻ x, ⨆ θ, ENNReal.ofReal (q θ x) ∂μ ≤
      1 + ENNReal.ofReal Real.pi *
        (ENNReal.ofReal (1 / Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi, fisherInfo μ q θ) ^ (1 / 2 : ℝ) := by
  let _ := sigmaPositive μ (q 0) (hpos 0) (hmeas 0) (hnorm 0)
  let ν := (volume : Measure ℝ).restrict (Set.Ico 0 Real.pi)
  let Q := fun z : ℝ × X => ENNReal.ofReal (q z.1 z.2)
  let d := fun z : ℝ × X => deriv (fun t => q t z.2) z.1
  let D := fun z : ℝ × X => ENNReal.ofReal |d z|
  let I := fun z : ℝ × X => ENNReal.ofReal (q z.1 z.2 * (d z / q z.1 z.2)^2)
  have hq : Measurable (Function.uncurry q) :=
    measurable_uncurry_of_continuous_of_measurable (fun x => (hC1 x).continuous) hmeas
  have hd : Measurable d := derivMeasurable q hC1 hmeas
  have hQ : Measurable Q := hq.ennreal_ofReal
  have hD : Measurable D := hd.abs.ennreal_ofReal
  have hI : Measurable I := (hq.mul ((hd.div hq).pow_const 2)).ennreal_ofReal
  have factor (z : ℝ × X) : Q z ^ (1/2 : ℝ) * I z ^ (1/2 : ℝ) = D z := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    dsimp only [Q,I,D]
    rw [← ENNReal.ofReal_mul (hpos _ _).le]
    have he : q z.1 z.2 * (q z.1 z.2 * (d z / q z.1 z.2)^2) = |d z|^2 := by
      rw [sq_abs]; field_simp [(hpos _ _).ne']
    rw [he, ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq (abs_nonneg _)]
  have intQ : ∫⁻ z, Q z ∂ν.prod μ = ENNReal.ofReal Real.pi := by
    rw [lintegral_prod Q hQ.aemeasurable]
    dsimp only [Q]
    simp [hnorm, ν, Real.volume_Ico]
  have intI : ∫⁻ z, I z ∂ν.prod μ = ∫⁻ t in Set.Ico 0 Real.pi, fisherInfo μ q t := by
    rw [lintegral_prod I hI.aemeasurable]
    refine lintegral_congr fun t => lintegral_congr fun x => ?_
    have hh : deriv (fun s => Real.log (q s x)) t = d (t,x) / q t x :=
      (((hC1 x).differentiable_one t).hasDerivAt.log (hpos t x).ne').deriv
    simp only [I, hh, ENNReal.ofReal_mul (hpos t x).le]
  have hold := ENNReal.lintegral_mul_le_Lp_mul_Lq (ν.prod μ)
    (show Real.HolderConjugate 2 2 from Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩)
    (hQ.pow_const (1/2 : ℝ)).aemeasurable (hI.pow_const (1/2 : ℝ)).aemeasurable
  change (∫⁻ z, Q z ^ (1/2 : ℝ) * I z ^ (1/2 : ℝ) ∂ν.prod μ) ≤ _ at hold
  simp only [factor, ← ENNReal.rpow_mul, show (1/2 : ℝ) * 2 = 1 by norm_num,
    ENNReal.rpow_one, intQ, intI] at hold
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (q 0 x) + ∫⁻ t, D (t,x) ∂ν ∂μ :=
      lintegral_mono fun x => iSup_le fun t => anchored (hC1 x) (fun y => hper y x) (hpos _ _).le t
    _ = 1 + ∫⁻ z, D z ∂ν.prod μ := by
      rw [lintegral_add_left (hmeas 0).ennreal_ofReal, hnorm, lintegral_prod_symm D hD.aemeasurable]
    _ ≤ _ := by rw [← normalizeRoot]; exact add_le_add_right hold 1
