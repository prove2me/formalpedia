-- Prove2me | solution 1 for ManyServerQED.Scheduling.weighted_lipschitz_path_has_measurable_drift_density
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:40:29.844399+00:00
-- url     : https://prove2.me/submissions/30263721-e4fc-4068-9781-d3958da588c2

import Mathlib

open Filter Topology Set MeasureTheory
open scoped NNReal

set_option maxHeartbeats 900000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (A : Ω → ℝ → (Fin k → ℝ)) (R : Ω → ℝ → ℝ)
    (hA : Measurable (fun z : Ω × ℝ => A z.1 z.2))
    (hR : Measurable (fun z : Ω × ℝ => R z.1 z.2))
    (hRc : ∀ ω, Continuous (R ω)) (hRn : ∀ ω t, 0 ≤ R ω t)
    (hLip : ∀ ω s t C, 0 ≤ s → 0 ≤ t →
      (∀ u ∈ uIcc s t, R ω u ≤ C) → ‖A ω t - A ω s‖ ≤ C*|t-s|) :
    ∃ b : Ω → ℝ → Fin k → ℝ,
      Measurable (fun z : Ω × ℝ => b z.1 z.2) ∧
      (∀ ω t, ‖b ω t‖ ≤ R ω t) ∧
      ∀ ω T, 0 ≤ T → (∫ s in (0:ℝ)..T, b ω s) = A ω T - A ω 0 := by
  let step (n : ℕ) := 1/((n:ℝ)+1)
  let q (i : Fin k) (n : ℕ) (z : Ω × ℝ) :=
    (step n)⁻¹ * (A z.1 (z.2+step n) i-A z.1 z.2 i)
  have hq (i : Fin k) (n : ℕ) : Measurable (q i n) := by
    let m := measurable_pi_apply (X := fun _ : Fin k => ℝ) i
    exact ((m.comp (hA.comp (measurable_fst.prodMk (measurable_snd.add_const _)))).sub
      (m.comp hA)).const_mul _
  let v (i : Fin k) (z : Ω × ℝ) := limUnder atTop (fun n => q i n z)
  have hv (i : Fin k) : Measurable (v i) :=
    (StronglyMeasurable.limUnder (fun n => (hq i n).stronglyMeasurable)).measurable
  let b (ω : Ω) (t : ℝ) (i : Fin k) := max (-R ω t) (min (R ω t) (v i (ω,t)))
  have hb : Measurable (fun z : Ω × ℝ => b z.1 z.2) := by
    apply measurable_pi_lambda
    intro i
    exact hR.neg.max (hR.min (hv i))
  have hbn (ω : Ω) (t : ℝ) : ‖b ω t‖ ≤ R ω t := by
    apply (pi_norm_le_iff_of_nonneg (hRn ω t)).2
    intro i
    rw [Real.norm_eq_abs,abs_le]
    exact ⟨le_max_left _ _,max_le (by linarith [hRn ω t]) (min_le_left _ _)⟩
  refine ⟨b,hb,hbn,?_⟩
  intro ω T hT
  have hM : ∃ C ≥ (0:ℝ), ∀ s ∈ Icc (0:ℝ) T, R ω s ≤ C := by
    obtain ⟨C,hC⟩ := (isCompact_Icc.image_of_continuousOn (hRc ω).continuousOn).bddAbove
    exact ⟨max 0 C,le_max_left _ _,fun s hs => (hC ⟨s,hs,rfl⟩).trans (le_max_right _ _)⟩
  obtain ⟨C,hC,hRC⟩ := hM
  let f (i : Fin k) (s : ℝ) := A ω s i
  have hF (i : Fin k) : LipschitzOnWith ⟨C,hC⟩ (f i) (Icc 0 T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht s hs
    have hsub : uIcc s t ⊆ Icc 0 T := uIcc_subset_Icc hs ht
    have hnorm := hLip ω s t C hs.1 ht.1 (fun u hu => hRC u (hsub hu))
    calc
      dist (f i t) (f i s) = ‖(A ω t - A ω s) i‖ := by rw [dist_eq_norm]; rfl
      _ ≤ ‖A ω t - A ω s‖ := norm_le_pi_norm _ _
      _ ≤ C * dist t s := by simpa only [Real.dist_eq] using hnorm
  have hAC (i : Fin k) : AbsolutelyContinuousOnInterval (f i) 0 T :=
    LipschitzOnWith.absolutelyContinuousOnInterval (by simpa only [uIcc_of_le hT] using hF i)
  have hDeriv (i : Fin k) (s : ℝ) (hs : 0 < s) : ‖deriv (f i) s‖ ≤ R ω s := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hOpen := (isOpen_Ioi (a := (0:ℝ))).inter (isOpen_lt (hRc ω) continuous_const :
      IsOpen {u | R ω u < R ω s + ε})
    have hsU : s ∈ Ioi 0 ∩ {u | R ω u < R ω s+ε} := ⟨hs,by simp [hε]⟩
    obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.1 (hOpen.mem_nhds hsU)
    apply norm_deriv_le_of_lip' (by linarith [hRn ω s] : 0 ≤ R ω s+ε)
    filter_upwards [Metric.ball_mem_nhds s hr] with t ht
    have hsB : s ∈ Metric.ball s r := Metric.mem_ball_self hr
    have huB : uIcc s t ⊆ Metric.ball s r := by
      rw [Real.ball_eq_Ioo] at ht hsB ⊢
      intro u hu
      exact ⟨(lt_min hsB.1 ht.1).trans_le hu.1,hu.2.trans_lt (max_lt hsB.2 ht.2)⟩
    have hN := hLip ω s t (R ω s+ε) hs.le (hrU ht).1.le
      (fun u hu => (hrU (huB hu)).2.le)
    exact (norm_le_pi_norm (A ω t-A ω s) i).trans (by simpa only [Real.norm_eq_abs] using hN)
  have hstep : Tendsto step atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · change Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0)
      apply tendsto_const_nhds.div_atTop
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    · exact Eventually.of_forall (fun n => by change 0 < step n; dsimp [step]; positivity)
  have hEq (i : Fin k) (s : ℝ) (hs : 0 < s) (hd : DifferentiableAt ℝ (f i) s) :
      b ω s i = deriv (f i) s := by
    have hD := hd.hasDerivAt.tendsto_slope_zero_right.comp hstep
    have heq : v i (ω,s) = deriv (f i) s := by
      exact hD.limUnder_eq
    have hr := hDeriv i s hs
    rw [Real.norm_eq_abs,abs_le] at hr
    dsimp only [b]
    rw [heq,min_eq_right hr.2,max_eq_right hr.1]
  have hbI : IntervalIntegrable (fun s => b ω s) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
      ((integrable_const C).mono' (hb.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs =>
          (hbn ω s).trans (hRC s ⟨hs.1.le,hs.2⟩))))
  ext i
  let L : (Fin k → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hp := L.intervalIntegral_comp_comm hbI
  change (∫ s in (0:ℝ)..T, b ω s i) = (∫ s in (0:ℝ)..T, b ω s) i at hp
  rw [← hp]
  change (∫ s in (0:ℝ)..T, b ω s i) = f i T-f i 0
  rw [← (hAC i).integral_deriv_eq_sub]
  rw [intervalIntegral.integral_of_le hT,intervalIntegral.integral_of_le hT]
  apply integral_congr_ae
  apply (ae_restrict_iff' measurableSet_Ioc).2
  filter_upwards [(hAC i).ae_differentiableAt] with s hd hs
  exact hEq i s hs.1 (hd (by rw [uIcc_of_le hT]; exact ⟨hs.1.le,hs.2⟩))
