-- Prove2me | solution 1 for GittinsUCB.Patient.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:38:44.252446+00:00
-- url     : https://prove2.me/submissions/2d5a3415-4bbd-4163-b027-bfb04236d7a0

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
import Theorems.Thm_GittinsUCB_Patient_equation_5
import Theorems.Thm_GittinsUCB_Patient_lemma_4
import Theorems.Thm_GittinsUCB_Patient_lemma_7
import Theorems.Thm_GittinsUCB_Patient_explore_then_commit
import Theorems.Thm_GittinsUCB_Patient_posterior_mean_law
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal
open GittinsUCB.Patient

lemma aux_inv_bound (x pv v : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 4) (hpv : pv ≤ x)
    (hv : v = 1 - pv) (hv0 : 0 < v) : 1 / v ≤ 1 + 2 * x := by
  rw [div_le_iff₀ hv0]
  have h1 : (1 + 2 * x) * (1 - x) ≤ (1 + 2 * x) * v :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : 0 ≤ x * (1 - 2 * x) := mul_nonneg hx0 (by linarith)
  have h3 : (1 + 2 * x) * (1 - x) = 1 + x * (1 - 2 * x) := by ring
  linarith

lemma aux_quad (lam v u : ℝ) (hv0 : 0 < v) (hu2 : 2 ≤ u) (hl2 : lam ^ 2 ≤ 2 * u)
    (hvinv : 1 / v ≤ 1 + 2 * (u ^ 2)⁻¹) : lam ^ 2 / v / 2 ≤ lam ^ 2 / 2 + 1 := by
  have e : lam ^ 2 / v / 2 = lam ^ 2 / 2 * (1 / v) := by ring
  rw [e]
  have h1 : lam ^ 2 / 2 * (1 / v) ≤ lam ^ 2 / 2 * (1 + 2 * (u ^ 2)⁻¹) :=
    mul_le_mul_of_nonneg_left hvinv (by positivity)
  have hu0 : 0 < u := by linarith
  have h2 : lam ^ 2 * (u ^ 2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    have : 2 * u ≤ u ^ 2 := by nlinarith
    linarith
  have e2 : lam ^ 2 / 2 * (1 + 2 * (u ^ 2)⁻¹) = lam ^ 2 / 2 + lam ^ 2 * (u ^ 2)⁻¹ := by ring
  linarith

set_option maxHeartbeats 1000000 in
theorem solution (σW2 : ℝ≥0) (hW : 0 < σW2) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ γ : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
        Real.sqrt (2 * Real.log (1 / (1 - γ))) - ε ≤
          gittinsIndex σW2 γ 0 1 := by
  intro ε0 hε0
  set ε := min ε0 1 with hεdef
  have hε : 0 < ε := lt_min hε0 one_pos
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεε0 : ε ≤ ε0 := min_le_left _ _
  set s : ℝ := (σW2 : ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact_mod_cast hW
  -- u(γ) = log (1/(1-γ)) → +∞
  have hu : Tendsto (fun γ : ℝ => Real.log (1 / (1 - γ)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) atTop := by
    have h1 : Tendsto (fun γ : ℝ => 1 - γ) (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun γ : ℝ => 1 - γ) (nhds 1) (nhds (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with γ hγ
        simp only [Set.mem_Iio] at hγ
        simp only [Set.mem_Ioi]; linarith
    have h2 := tendsto_inv_nhdsGT_zero.comp h1
    refine Real.tendsto_log_atTop.comp (h2.congr ?_)
    intro γ; simp
  have hlog : Real.log =o[atTop] Real.sqrt := by
    have := isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)
    refine this.congr_right ?_
    intro x; rw [Real.sqrt_eq_rpow]
  -- eventual properties of `u`
  have hP : ∀ᶠ u : ℝ in atTop, 2 ≤ u ∧ (2 + ε) ^ 2 / 2 ≤ u ∧ 2 ≤ s * u ^ 2 ∧
      2 * Real.log u ≤ ε / 4 * Real.sqrt u ∧ 5 ≤ ε / 2 * Real.sqrt u := by
    refine (eventually_ge_atTop 2).and ((eventually_ge_atTop _).and
      (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)))
    · exact ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hs0).eventually_ge_atTop 2
    · have := hlog.def (c := ε / 8) (by positivity)
      filter_upwards [this, eventually_ge_atTop 1] with u hu hu1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hu1),
        abs_of_nonneg (Real.sqrt_nonneg _)] at hu
      linarith
    · have : Tendsto (fun u => ε / 2 * Real.sqrt u) atTop atTop :=
        Real.tendsto_sqrt_atTop.const_mul_atTop (by positivity)
      exact this.eventually_ge_atTop 5
  have hPγ := hu.eventually hP
  have h7 := (lemma_7 σW2 hW).def (c := ε / 4) (by positivity)
  have hev : ∀ᶠ γ : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1), γ ∈ Set.Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsLT (by norm_num)
  filter_upwards [hPγ, h7, hev] with γ hP h7 hγ
  obtain ⟨hu2, hue, hsu, hlogu, h5⟩ := hP
  obtain ⟨hγ0, hγ1⟩ := hγ
  have h1γ : 0 < 1 - γ := by linarith
  set u := Real.log (1 / (1 - γ)) with hu_def
  clear_value u
  set a := Real.sqrt (2 * u) with ha_def
  clear_value a
  have ha2u : a ^ 2 = 2 * u := by rw [ha_def]; exact Real.sq_sqrt (by linarith)
  have ha0 : 0 ≤ a := by rw [ha_def]; exact Real.sqrt_nonneg _
  have hsqu0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
  have hau : Real.sqrt u ≤ a := by rw [ha_def]; exact Real.sqrt_le_sqrt (by linarith)
  have hae : 2 + ε ≤ a := by
    rw [ha_def]; apply Real.le_sqrt_of_sq_le; linarith
  have ha2 : 2 ≤ a := by linarith
  -- the set of admissible taxes is bounded above by `a`
  have hbound : ∀ lam ∈ {lam : ℝ | 0 ≤ value σW2 γ lam 0 1}, lam ≤ a := by
    intro lam hlam
    simp only [Set.mem_setOf_eq] at hlam
    by_contra hlt
    rw [not_le] at hlt
    have hlam2 : 2 ≤ lam := by linarith
    have h5 := equation_5 σW2 hW γ lam hγ0 hγ1
    have hint : (∫ ω, max (θ ω - lam) 0 ∂(model 0 1 σW2)) =
        ∫ x : ℝ, max (x - lam) 0 ∂(gaussianReal 0 1) := by
      unfold model θ
      exact (integral_fun_fst (μ := gaussianReal 0 1) (fun x : ℝ => max (x - lam) 0)).trans
        (by simp)
    have h4 := (lemma_4 1 lam one_pos (by linarith)).2
    have e : (gaussianReal 0 ⟨(1:ℝ) ^ 2, sq_nonneg 1⟩ : Measure ℝ) = gaussianReal 0 1 := by
      congr 1; exact NNReal.eq (show ((1:ℝ)^2) = 1 by norm_num)
    rw [e, ← hint, div_one, one_mul] at h4
    have hc : 0 ≤ γ / (1 - γ) := by positivity
    have key : lam ≤ γ / (1 - γ) * stdPdf lam := by
      have := mul_le_mul_of_nonneg_left h4 hc
      linarith
    unfold stdPdf at key
    set E := Real.exp (-lam ^ 2 / 2) with hE
    have hpi : 1 ≤ Real.sqrt (2 * Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      have := Real.pi_gt_three; linarith
    have k2 : (1 - γ) ≤ γ * E := by
      have : lam * (1 - γ) * Real.sqrt (2 * Real.pi) ≤ γ * E := by
        rw [div_mul_div_comm, le_div_iff₀ (by positivity)] at key
        nlinarith
      have : 1 - γ ≤ lam * (1 - γ) * Real.sqrt (2 * Real.pi) := by
        have h1 : 1 ≤ lam * Real.sqrt (2 * Real.pi) := by nlinarith
        nlinarith
      linarith
    have k3 : 1 - γ ≤ E := by
      have : γ * E ≤ E := by
        have := Real.exp_pos (-lam ^ 2 / 2)
        nlinarith
      linarith
    have k4 : Real.log (1 - γ) ≤ -lam ^ 2 / 2 := by
      rw [hE] at k3
      have := Real.log_le_log h1γ k3
      rwa [Real.log_exp] at this
    have k5 : lam ^ 2 ≤ 2 * u := by
      rw [hu_def, one_div, Real.log_inv]; linarith
    have : lam ≤ a := by
      rw [ha_def]; exact Real.le_sqrt_of_sq_le k5
    linarith
  -- the exploration length and posterior variance
  have hLge' : s * Real.log (1 / (1 - γ)) ^ 2 ≤ (explorationLength s γ : ℝ) := Nat.le_ceil _
  set L : ℕ := explorationLength s γ with hL_def
  clear_value L
  have hLge : s * u ^ 2 ≤ (L : ℝ) := by rw [hu_def]; exact hLge'
  have hL2 : 2 ≤ L := by
    have : (2 : ℝ) ≤ L := le_trans hsu hLge
    exact_mod_cast this
  have hL0 : (0 : ℝ) < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL2
    linarith
  set pv := postVar 1 s L with hpv_def
  clear_value pv
  have hpv0 : 0 < pv := by
    rw [hpv_def]; unfold postVar; positivity
  have hpvle : pv ≤ (u ^ 2)⁻¹ := by
    rw [hpv_def]; unfold postVar
    apply inv_anti₀ (by positivity)
    have : u ^ 2 ≤ (L : ℝ) / s := by rw [le_div_iff₀ hs0]; linarith
    linarith
  set v := 1 - pv with hv_def
  clear_value v
  have hu4 : 4 ≤ u ^ 2 := by
    calc (4:ℝ) = 2 ^ 2 := by norm_num
      _ ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) hu2 2
  have hx : (u ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have hv0 : 0 < v := by linarith
  have hv1 : v ≤ 1 := by linarith
  have hvinv : 1 / v ≤ 1 + 2 * (u ^ 2)⁻¹ :=
    aux_inv_bound _ pv v (by positivity) hx hpvle hv_def hv0
  -- the candidate tax
  set lam := a - ε with hlam_def
  clear_value lam
  have hlam2 : 2 ≤ lam := by linarith
  have hlam0 : 0 < lam := by linarith
  set σ := Real.sqrt v with hσ_def
  clear_value σ
  have hσ0 : 0 < σ := by rw [hσ_def]; exact Real.sqrt_pos.mpr hv0
  have hσ1 : σ ≤ 1 := by rw [hσ_def, Real.sqrt_le_one]; exact hv1
  have hσ2 : σ ^ 2 = v := by rw [hσ_def]; exact Real.sq_sqrt hv0.le
  -- measurability of the posterior mean
  have hmeas : ∀ t, Measurable (postMean 0 1 s t) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ n ih =>
      have hR : Measurable (R n) :=
        measurable_fst.add ((measurable_pi_apply n).comp measurable_snd)
      show Measurable (fun ω => (postMean 0 1 s n ω / postVar 1 s n + R n ω / s) /
        (1 / postVar 1 s n + 1 / s))
      exact ((ih.div_const _).add (hR.div_const _)).div_const _
  -- the expected positive part of μ_L - lam
  have hlaw := posterior_mean_law σW2 hW L 0
  have hEint : (∫ ω, max (postMean 0 1 s L ω - lam) 0 ∂(model 0 1 σW2)) =
      ∫ x : ℝ, max (x - lam) 0 ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) := by
    have e : (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩ : Measure ℝ) =
        gaussianReal 0 (1 - postVar 1 s L).toNNReal := by
      congr 1; apply NNReal.eq
      show σ ^ 2 = ((1 - postVar 1 s L).toNNReal : ℝ)
      rw [← hpv_def, ← hv_def, Real.coe_toNNReal _ hv0.le, hσ2]
    rw [e, ← hlaw]
    rw [integral_map (hmeas L).aemeasurable]
    exact ((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable
  have h4 := (lemma_4 σ lam hσ0 (by linarith)).1
  rw [← hEint] at h4
  have hetc := (explore_then_commit σW2 hW γ lam hγ0 hγ1 L hL2).2 hlam0.le
  -- the key inequality  L·lam ≤ γ^L/(1-γ) · σ⁴/lam³ · φ(lam/σ)
  have hσ4 : σ ^ 4 = v ^ 2 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, hσ2]
  have hφ : stdPdf (lam / σ) = Real.exp (-(lam ^ 2 / v) / 2) / Real.sqrt (2 * Real.pi) := by
    unfold stdPdf; rw [div_pow, hσ2]
  set c := Real.log (Real.sqrt (2 * Real.pi)) with hc_def
  clear_value c
  have hpi1 : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have := Real.pi_gt_three; linarith
  have hc0 : 0 ≤ c := by rw [hc_def]; exact Real.log_nonneg hpi1
  have hc1 : c ≤ 1 := by
    rw [hc_def, Real.log_le_iff_le_exp (by linarith),
      Real.sqrt_le_left (by positivity)]
    have he := Real.exp_one_gt_d9
    have hp := Real.pi_lt_d2
    nlinarith
  have hγL : 0 < γ ^ L := pow_pos hγ0 L
  have hRHSpos : 0 < γ ^ L / (1 - γ) * (σ ^ 4 / lam ^ 3 * stdPdf (lam / σ)) := by
    rw [hφ]; positivity
  have hlogR : Real.log (γ ^ L / (1 - γ) * (σ ^ 4 / lam ^ 3 * stdPdf (lam / σ))) =
      (L : ℝ) * Real.log γ + u + 2 * Real.log v - 3 * Real.log lam -
        lam ^ 2 / v / 2 - c := by
    rw [hσ4, hφ]
    have e1 : Real.log (1 - γ) = -u := by
      rw [hu_def, one_div, Real.log_inv, neg_neg]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity)
      (by positivity), Real.log_pow, e1, Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_div (by positivity) (by positivity), Real.log_exp, ← hc_def]
    push_cast; ring
  have hh : hAux s γ = -Real.log L + (L : ℝ) * Real.log γ + 2 * Real.log v + c := by
    unfold hAux; rw [← hL_def, ← hpv_def, ← hv_def, ← hc_def]
  have h7' : -(ε / 4 * Real.sqrt u) ≤ hAux s γ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsqu0] at h7
    exact neg_le_of_abs_le h7
  -- bounds on the quadratic and logarithmic terms
  have hlam_sq : lam ^ 2 / 2 = u - ε * a + ε ^ 2 / 2 := by
    rw [hlam_def]; linear_combination ha2u / 2
  have hquad : lam ^ 2 / v / 2 ≤ u - ε * a + ε ^ 2 / 2 + 1 := by
    have hl2 : lam ^ 2 ≤ 2 * u := by
      rw [← ha2u]; exact pow_le_pow_left₀ hlam0.le (by linarith) 2
    have := aux_quad lam v u hv0 hu2 hl2 hvinv
    linarith
  have hloglam : 4 * Real.log lam ≤ 2 * Real.log 2 + 2 * Real.log u := by
    have h1 : Real.log lam ≤ Real.log a := Real.log_le_log hlam0 (by linarith)
    have h2 : 2 * Real.log a = Real.log 2 + Real.log u := by
      have e : Real.log (a ^ 2) = 2 * Real.log a := by rw [Real.log_pow]; norm_num
      rw [← e, ha2u, Real.log_mul (by norm_num) (by linarith)]
    linarith
  have hlog2 := Real.log_two_lt_d9
  have hlogineq : Real.log ((L : ℝ) * lam) ≤
      Real.log (γ ^ L / (1 - γ) * (σ ^ 4 / lam ^ 3 * stdPdf (lam / σ))) := by
    rw [hlogR, Real.log_mul hL0.ne' hlam0.ne']
    have : (L : ℝ) * Real.log γ + 2 * Real.log v = hAux s γ + Real.log L - c := by
      rw [hh]; ring
    have hεa : ε * Real.sqrt u ≤ ε * a := mul_le_mul_of_nonneg_left hau hε.le
    have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
    linarith
  have hkey : (L : ℝ) * lam ≤ γ ^ L / (1 - γ) * (σ ^ 4 / lam ^ 3 * stdPdf (lam / σ)) :=
    (Real.log_le_log_iff (by positivity) hRHSpos).mp hlogineq
  have hval : 0 ≤ value σW2 γ lam 0 1 := by
    have hc' : 0 ≤ γ ^ L / (1 - γ) := by positivity
    have := mul_le_mul_of_nonneg_left h4 hc'
    have hetc' : -(L : ℝ) * lam + γ ^ L / (1 - γ) *
        ∫ ω, max (postMean 0 1 s L ω - lam) 0 ∂(model 0 1 σW2) ≤ value σW2 γ lam 0 1 :=
      hetc
    linarith
  have hmem : lam ∈ {lam : ℝ | 0 ≤ value σW2 γ lam 0 1} := hval
  have hS : lam ≤ gittinsIndex σW2 γ 0 1 := le_csSup ⟨a, hbound⟩ hmem
  linarith
