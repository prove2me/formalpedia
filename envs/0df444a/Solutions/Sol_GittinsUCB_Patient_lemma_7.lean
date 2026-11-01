-- Prove2me | solution 1 for GittinsUCB.Patient.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:25:55.496789+00:00
-- url     : https://prove2.me/submissions/108d2e5a-c53e-4b22-b22c-0c1a9f7a082f

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal
open GittinsUCB.Patient

theorem solution (σW2 : ℝ≥0) (hW : 0 < σW2) :
    (fun γ : ℝ => hAux (σW2 : ℝ) γ) =o[nhdsWithin (1 : ℝ) (Set.Iio 1)]
      (fun γ : ℝ => Real.sqrt (Real.log (1 / (1 - γ)))) := by
  set s : ℝ := (σW2 : ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact_mod_cast hW
  -- generic: a convergent function is o(√·) at +∞
  have lo_of_tendsto : ∀ {f : ℝ → ℝ} {c : ℝ}, Tendsto f atTop (nhds c) →
      f =o[atTop] Real.sqrt := by
    intro f c h
    have h1 : f =O[atTop] (fun _ => (1:ℝ)) := h.isBigO_one ℝ
    have h2 : (fun _ => (1:ℝ)) =o[atTop] Real.sqrt := by
      rw [isLittleO_one_left_iff]
      refine (tendsto_abs_atTop_atTop.comp Real.tendsto_sqrt_atTop).congr ?_
      intro x; simp [Real.norm_eq_abs]
    exact h1.trans_isLittleO h2
  set Lf : ℝ → ℝ := fun u => ((⌈s * u ^ 2⌉₊ : ℕ) : ℝ) with hLf
  have hsq : Tendsto (fun u : ℝ => s * u ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop hs0
  have hLtop : Tendsto Lf atTop atTop :=
    tendsto_atTop_mono (fun u => Nat.le_ceil _) hsq
  have hLup : ∀ u, Lf u ≤ s * u ^ 2 + 1 := by
    intro u
    have : 0 ≤ s * u ^ 2 := by positivity
    exact (Nat.ceil_lt_add_one this).le
  -- Term 1: log L = o(√u)
  have T1 : (fun u => Real.log (Lf u)) =o[atTop] Real.sqrt := by
    have hlog : Real.log =o[atTop] Real.sqrt := by
      have := isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)
      refine this.congr_right ?_
      intro x; rw [Real.sqrt_eq_rpow]
    refine IsBigO.trans_isLittleO ?_ hlog
    refine IsBigO.of_bound (|Real.log (s + 1)| + 2) ?_
    have hL1 : ∀ᶠ u in atTop, 1 ≤ Lf u := hLtop.eventually_ge_atTop 1
    filter_upwards [hL1, eventually_ge_atTop (Real.exp 1)] with u hu1 hue
    have hu0 : 1 ≤ u := le_trans (by
      have := Real.add_one_le_exp (1:ℝ); linarith) hue
    have hlu : 1 ≤ Real.log u := by
      rw [Real.le_log_iff_exp_le (by linarith)]; exact hue
    have hlogL0 : 0 ≤ Real.log (Lf u) := Real.log_nonneg hu1
    have hLb : Lf u ≤ (s + 1) * u ^ 2 := by
      have := hLup u
      have : 1 ≤ u ^ 2 := one_le_pow₀ hu0
      nlinarith
    have hlogLb : Real.log (Lf u) ≤ Real.log (s + 1) + 2 * Real.log u := by
      calc Real.log (Lf u) ≤ Real.log ((s + 1) * u ^ 2) :=
            Real.log_le_log (by linarith) hLb
        _ = Real.log (s + 1) + 2 * Real.log u := by
            rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]; norm_num
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogL0,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.log u)]
    have : Real.log (s + 1) ≤ |Real.log (s + 1)| * Real.log u := by
      calc Real.log (s + 1) ≤ |Real.log (s + 1)| := le_abs_self _
        _ ≤ |Real.log (s + 1)| * Real.log u := by
          have := abs_nonneg (Real.log (s + 1)); nlinarith
    nlinarith
  -- Term 2: L * log(1 - e^{-u}) → 0
  have T2 : Tendsto (fun u => Lf u * Real.log (1 - Real.exp (-u))) atTop (nhds 0) := by
    have hB : Tendsto (fun u : ℝ => 2 * (s * (u ^ 2 * Real.exp (-u)) + Real.exp (-u)))
        atTop (nhds 0) := by
      have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero
      simpa using ((h1.const_mul s).add h2).const_mul 2
    refine squeeze_zero_norm' ?_ hB
    have hx : ∀ᶠ u : ℝ in atTop, Real.exp (-u) ≤ 1 / 2 := by
      filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
      have : Real.exp (-u) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg]
        have := Real.add_one_le_exp (1:ℝ)
        rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
      linarith
    filter_upwards [hx] with u hu
    set x := Real.exp (-u) with hxdef
    have hx0 : 0 < x := Real.exp_pos _
    have h1x : 0 < 1 - x := by linarith
    have hlog_le : Real.log (1 - x) ≤ 0 := Real.log_nonpos h1x.le (by linarith)
    have hlog_ge : 1 - (1 - x)⁻¹ ≤ Real.log (1 - x) := Real.one_sub_inv_le_log_of_pos h1x
    have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
      rw [inv_le_iff_one_le_mul₀ h1x]; nlinarith
    have habs : |Real.log (1 - x)| ≤ 2 * x := by
      rw [abs_of_nonpos hlog_le]; linarith
    have hL0 : 0 ≤ Lf u := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hL0]
    calc Lf u * |Real.log (1 - x)| ≤ (s * u ^ 2 + 1) * (2 * x) :=
          mul_le_mul (hLup u) habs (abs_nonneg _) (by positivity)
      _ = 2 * (s * (u ^ 2 * x) + x) := by ring
  -- Term 3: 2 log (1 - postVar) → 0
  have T3 : Tendsto (fun u => 2 * Real.log (1 - postVar 1 s ⌈s * u ^ 2⌉₊)) atTop (nhds 0) := by
    have hpv : Tendsto (fun u => postVar 1 s ⌈s * u ^ 2⌉₊) atTop (nhds 0) := by
      unfold postVar
      have : Tendsto (fun u => 1 / (1:ℝ) + Lf u / s) atTop atTop := by
        refine tendsto_atTop_add_const_left _ _ ?_
        exact hLtop.atTop_div_const hs0
      exact tendsto_inv_atTop_zero.comp this
    have h1 : Tendsto (fun u => 1 - postVar 1 s ⌈s * u ^ 2⌉₊) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hpv
    have h2 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1).const_mul 2
    simpa using h2
  -- assemble on the `u` side
  set H : ℝ → ℝ := fun u => -Real.log (Lf u) + Lf u * Real.log (1 - Real.exp (-u)) +
      2 * Real.log (1 - postVar 1 s ⌈s * u ^ 2⌉₊) + Real.log (Real.sqrt (2 * Real.pi)) with hH
  have hHo : H =o[atTop] Real.sqrt :=
    ((T1.neg_left.add (lo_of_tendsto T2)).add (lo_of_tendsto T3)).add
      (lo_of_tendsto (tendsto_const_nhds (x := Real.log (Real.sqrt (2 * Real.pi)))))
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
  have hcomp := hHo.comp_tendsto hu
  refine hcomp.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  simp only [Set.mem_Iio] at hγ
  have h1γ : 0 < 1 - γ := by linarith
  have hexp : Real.exp (-Real.log (1 / (1 - γ))) = 1 - γ := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]; simp
  simp only [Function.comp, hH, hLf, hAux, explorationLength]
  rw [hexp]
  ring_nf
