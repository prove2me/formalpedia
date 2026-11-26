-- Prove2me | solution 1 for ManyServerQED.Scheduling.finite_dimensional_cadlag_processes_have_compact_subsequence_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:13:57.790957+00:00
-- url     : https://prove2.me/submissions/71532026-2172-4895-af73-7c0f37e6744b

import Theorems.Thm_ManyServerQED_Scheduling_bounded_unit_process_subsequence_finite_observation_limit
import Theorems.Thm_ManyServerQED_Scheduling_weighted_arctangent_time_compression_transfers_modulus
import Theorems.Thm_ManyServerQED_Scheduling_functional_coupling_from_fdd_and_interval_modulus
import Theorems.Thm_ManyServerQED_Scheduling_arctangent_path_coupling_recovers_original_paths
import Theorems.Thm_ManyServerQED_Scheduling_arctangent_fdd_limit_is_interior_on_compact_rational_times
import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_Reiman84_QueueLength_Paths

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy Reiman84.QueueLength

private noncomputable def compressedTime (s : ℝ) : ℝ := s/(1-s)
private noncomputable def timeLeft (s : ℝ) : ℝ := max 0 (1-s)
private noncomputable def unitEmbed (t : ℝ) : ℝ := max t 0/(1+max t 0)
private noncomputable def unweight (t : ℝ) : ℝ := 1+max t 0

private noncomputable def arctanVector {k : ℕ} (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i => Real.arctan (x i)

private noncomputable def compactify {k : ℕ} (x : ℝ → Fin k → ℝ) (s : ℝ) :
    Fin k → ℝ := timeLeft s • arctanVector (x (compressedTime s))

private theorem continuous_arctanVector {k : ℕ} : Continuous (arctanVector (k := k)) :=
  continuous_pi (fun i => Real.continuous_arctan.comp (continuous_apply i))

private theorem norm_arctanVector {k : ℕ} (x : Fin k → ℝ) :
    ‖arctanVector x‖ ≤ Real.pi/2 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ Real.pi/2)).2
  intro i
  rw [Real.norm_eq_abs]
  exact (abs_lt.2 (Real.arctan_mem_Ioo (x i))).le

private theorem arctanVector_lip {k : ℕ} (x y : Fin k → ℝ) :
    ‖arctanVector x-arctanVector y‖ ≤ ‖x-y‖ := by
  have h : LipschitzWith 1 Real.arctan := by
    apply lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan
    intro x
    change ((‖deriv Real.arctan x‖₊ : ℝ) ≤ 1)
    rw [coe_nnnorm,Real.deriv_arctan,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact (div_le_one (show (0:ℝ) < 1+x^2 by positivity)).2
      (le_add_of_nonneg_right (sq_nonneg x))
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x-y))).2
  intro i
  have hh := h.dist_le_mul (x i) (y i)
  simpa only [arctanVector,Real.norm_eq_abs,Real.dist_eq,NNReal.coe_one,one_mul,Pi.sub_apply] using
    hh.trans (by simpa only [Real.dist_eq,Real.norm_eq_abs,NNReal.coe_one,one_mul,Pi.sub_apply] using
      norm_le_pi_norm (x-y) i)

private theorem continuousAt_compressedTime {s : ℝ} (hs : s < 1) :
    ContinuousAt compressedTime s :=
  continuous_id.continuousAt.div (continuous_const.sub continuous_id).continuousAt (by linarith)

private theorem continuous_timeLeft : Continuous timeLeft :=
  continuous_const.max (continuous_const.sub continuous_id)

private theorem timeLeft_eq {s : ℝ} (hs : s ≤ 1) : timeLeft s = 1-s :=
  max_eq_right (sub_nonneg.2 hs)

private theorem compressedTime_nonneg {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    0 ≤ compressedTime s := div_nonneg hs.1 (sub_nonneg.2 hs.2)

private theorem compressedTime_mono : StrictMonoOn compressedTime (Ico (0:ℝ) 1) := by
  intro s hs t ht hst
  apply (div_lt_div_iff₀ (sub_pos.2 hs.2) (sub_pos.2 ht.2)).2
  nlinarith only [hst]

private theorem continuous_unitEmbed : Continuous unitEmbed := by
  have hM : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
  exact hM.div (continuous_const.add hM) (fun t => by positivity)

private theorem unitEmbed_bounds {t : ℝ} (ht : 0 ≤ t) : unitEmbed t ∈ Ico (0:ℝ) 1 := by
  dsimp [unitEmbed]
  rw [max_eq_left ht]
  exact ⟨div_nonneg ht (by positivity),(div_lt_one (by positivity)).2 (by linarith)⟩

private theorem unitEmbed_mono : StrictMonoOn unitEmbed (Ici 0) := by
  intro s hs t ht hst
  unfold unitEmbed
  rw [max_eq_left hs,max_eq_left ht]
  apply (div_lt_div_iff₀ (by linarith [show 0 ≤ s from hs] : 0 < 1+s) (by linarith [show 0 ≤ t from ht] : 0 < 1+t)).2
  nlinarith only [hst]

private theorem compactify_inverse {k : ℕ} (f : ℝ → Fin k → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    unweight t • compactify f (unitEmbed t) = arctanVector (f t) := by
  have h := unitEmbed_bounds ht
  have hl : 1-unitEmbed t = (1+t)⁻¹ := by
    unfold unitEmbed
    rw [max_eq_left ht]
    field_simp
    ring
  have hC : compressedTime (unitEmbed t) = t := by
    unfold compressedTime
    rw [hl]
    unfold unitEmbed
    rw [max_eq_left ht]
    field_simp
  simp only [compactify, hC,timeLeft_eq h.2.le,hl,smul_smul,unweight,max_eq_left ht]
  rw [mul_inv_cancel₀ (by positivity : 1+t ≠ 0),one_smul]

private theorem norm_compactify {k : ℕ} (f : ℝ → Fin k → ℝ) {s : ℝ}
    (hs : s ≤ 1) : ‖compactify f s‖ ≤ (1-s)*(Real.pi/2) := by
  rw [compactify,norm_smul,timeLeft_eq hs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.2 hs)]
  exact mul_le_mul_of_nonneg_left (norm_arctanVector _) (sub_nonneg.2 hs)

private theorem compactify_one {k : ℕ} (f : ℝ → Fin k → ℝ) : compactify f 1 = 0 := by
  simp [compactify,timeLeft]

open ManyServerQED.Scheduling
private theorem rational_right_approximation {E : Type*} [PseudoMetricSpace E]
    {x : ℝ → E} {T : ℕ}
    (h : ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt x (Ici s) s)
    {s e : ℝ} (hs : s ∈ Icc (0:ℝ) (T:ℝ)) (he : 0 < e) :
    ∃ q : ℚ, (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ dist (q:ℝ) s < e ∧ dist (x q) (x s) < e := by
  rcases hs.2.lt_or_eq with hst | hst
  · obtain ⟨d,hd,hD⟩ := Metric.continuousWithinAt_iff.1 (h s hs.1) e he
    have hm : s < min (T:ℝ) (s+min d e) := lt_min hst
      (lt_add_of_pos_right _ (lt_min hd he))
    obtain ⟨q,hq,hQ⟩ := exists_rat_btwn hm
    have hdQ : dist (q:ℝ) s < min d e := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.2 hq)]
      linarith [(lt_min_iff.1 hQ).2]
    exact ⟨q,⟨hs.1.trans hq.le,(lt_min_iff.1 hQ).1.le⟩,(lt_min_iff.1 hdQ).2,
      hD hq.le (lt_min_iff.1 hdQ).1⟩
  · have hu : ((T:ℚ):ℝ) = s := by simpa using hst.symm
    exact ⟨T,by rw [hu]; exact hs,by rw [hu,dist_self]; exact he,
      by rw [hu,dist_self]; exact he⟩

private def marginSafe {k : ℕ} (p : ℝ≥0 → Fin k → ℝ) : Prop :=
  ∀ (T : ℕ) (i : Fin k), ∃ b : ℕ, ∀ q : ℚ, (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) →
      |p (q:ℝ).toNNReal i| ≤ Real.pi/2 - 1/((b:ℝ)+1)

private theorem margin_measurable {k : ℕ} :
    MeasurableSet {p : ℝ≥0 → Fin k → ℝ | marginSafe p} := by
  classical
  have he : {p : ℝ≥0 → Fin k → ℝ | marginSafe p} =
      ⋂ T : ℕ, ⋂ i : Fin k, ⋃ b : ℕ, ⋂ q : ℚ,
      {p : ℝ≥0 → Fin k → ℝ | (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) →
        |p (q:ℝ).toNNReal i| ≤ Real.pi/2 - 1/((b:ℝ)+1)} := by
    ext p
    simp only [Set.mem_setOf_eq,Set.mem_iInter,Set.mem_iUnion,marginSafe]
  rw [he]
  refine MeasurableSet.iInter fun T => MeasurableSet.iInter fun i =>
    MeasurableSet.iUnion fun b => MeasurableSet.iInter fun q => ?_
  by_cases hq : (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ)
  · simpa only [hq,true_implies,Function.comp_def] using
      measurableSet_le (((measurable_pi_apply i).comp (measurable_pi_apply (q:ℝ).toNNReal)).abs)
        (measurable_const (a := Real.pi/2-1/((b:ℝ)+1)))
  · simp [hq]

private theorem extend_margin {k : ℕ} {y : ℝ → Fin k → ℝ}
    (h : marginSafe (fun t : ℝ≥0 => y t))
    (hy : ∀ (i : Fin k) t, 0 ≤ t → ContinuousWithinAt (fun s => y s i) (Ici t) t)
    (T : ℕ) (i : Fin k) :
    ∃ C : ℝ, 0 ≤ C ∧ C < Real.pi/2 ∧ ∀ t ∈ Icc (0:ℝ) (T:ℝ), |y t i| ≤ C := by
  obtain ⟨b,hb⟩ := h T i
  let C := Real.pi/2-1/((b:ℝ)+1)
  have hC : 0 ≤ C := by
    refine (abs_nonneg (y 0 i)).trans ?_
    have hx : (((0:ℚ):ℝ)) ∈ Icc (0:ℝ) (T:ℝ) := by simpa using Nat.cast_nonneg (α := ℝ) T
    simpa [C] using hb 0 hx
  have hClt : C < Real.pi/2 := sub_lt_self _ (by positivity)
  refine ⟨C,hC,hClt,fun s hs => ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨q,hq,_,hqy⟩ := rational_right_approximation (hy i) hs hε
  have hB := hb q hq
  change |y ((q:ℝ).toNNReal:ℝ) i| ≤ C at hB
  rw [Real.coe_toNNReal _ hq.1] at hB
  rw [Real.dist_eq] at hqy
  have hh := abs_add_le (y s i - y q i) (y q i)
  rw [sub_add_cancel,abs_sub_comm] at hh
  linarith only [hh,hqy.le,hB]

private noncomputable def tangent_decode {k : ℕ} (p : ℝ≥0 → Fin k → ℝ) (t : ℝ≥0) (i : Fin k) : ℝ := by
  classical
  exact if marginSafe p then Real.tan (p t i) else 0

set_option maxHeartbeats 1800000 in
private theorem tangent_decode_measurable {k : ℕ} : Measurable (tangent_decode (k := k)) := by
  classical
  apply measurable_pi_lambda
  intro t
  apply measurable_pi_lambda
  intro i
  have htan : Measurable Real.tan := by
    rw [show Real.tan = (fun t : ℝ => Real.sin t/Real.cos t) from funext Real.tan_eq_sin_div_cos]
    exact Real.continuous_sin.measurable.div Real.continuous_cos.measurable
  have heval : Measurable (fun p : ℝ≥0 → Fin k → ℝ => p t i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply t)
  let f (p : ℝ≥0 → Fin k → ℝ) := Real.tan (p t i)
  have hf : Measurable f := htan.comp heval
  change Measurable (fun p : ℝ≥0 → Fin k → ℝ => if marginSafe p then f p else (0:ℝ))
  exact Measurable.ite (p := marginSafe) margin_measurable hf measurable_const


set_option maxHeartbeats 2100000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ)
    (hX : ∀ n ω i, IsCadlag (fun t => X n ω t i))
    (hXm : ∀ n t, 0 ≤ t → Measurable (fun ω => X n ω t))
    (hB : ∀ (T : ℕ) (η : ℝ), 0 < η → ∃ A ≥ (0:ℝ), ∀ᶠ n in atTop,
      P {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), A < ‖X n ω t‖} ≤ ENNReal.ofReal η)
    (hM : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (x : Ω' → ℝ → Fin k → ℝ),
        IsProbabilityMeasure P' ∧ (∀ ω, ContinuousOn (x ω) (Ici (0:ℝ))) ∧
        (∀ t, 0 ≤ t → Measurable (fun ω => x ω t)) ∧
        CouplingConverges P P' (fun n => X (r n)) x := by
  classical
  let I := Icc (0:ℝ) 1
  let E := Fin k → ℝ
  let Λ := C(I,E)
  letI : MeasurableSpace Λ := borel Λ
  letI : BorelSpace Λ := ⟨rfl⟩
  let Z (n : ℕ) (ω : Ω) := compactify (X n ω)
  have hZ (n : ℕ) (s : ℝ) (hs : s ∈ I) : Measurable (fun ω => Z n ω s) := by
    exact (continuous_arctanVector.measurable.comp (hXm n _ (compressedTime_nonneg hs))).const_smul
      (timeLeft s)
  have hZA (n : ℕ) (ω : Ω) (s : ℝ) (hs : s ∈ I) : ‖Z n ω s‖ ≤ Real.pi/2 :=
    (norm_compactify (X n ω) hs.2).trans (mul_le_of_le_one_left (by positivity) (by linarith [hs.1]))
  have hZM := weighted_arctangent_time_compression_transfers_modulus P X hM
  obtain ⟨r,hr,μ,hUL⟩ := bounded_unit_process_subsequence_finite_observation_limit Z hZ
    (Real.pi/2) hZA hZM
  let P' : Measure Λ := μ
  letI : IsProbabilityMeasure P' := μ.prop
  let time (t : ℝ) : I :=
    ⟨unitEmbed t,by
      have he : unitEmbed t = unitEmbed (max t 0) := by simp [unitEmbed,max_assoc]
      rw [he]
      have hb := unitEmbed_bounds (le_max_right t 0)
      exact ⟨hb.1,hb.2.le⟩⟩
  have hT : Continuous time := continuous_unitEmbed.subtype_mk _
  let v (ω : Λ) (t : ℝ) := unweight t • ω (time t)
  have hvc (ω : Λ) : Continuous (v ω) := by
    exact (continuous_const.add (continuous_id.max continuous_const)).smul (ω.continuous.comp hT)
  have hvm (t : ℝ) : Measurable (fun ω => v ω t) :=
    (continuous_eval_const (time t)).measurable.const_smul (unweight t)
  let Y (n : ℕ) (ω : Ω) (t : ℝ) := arctanVector (X (r n) ω t)
  have hF (m : ℕ) (τ : Fin m → ℝ) (hτ : ∀ i, 0 ≤ τ i) :
      TendstoInDistribution (fun n ω i => Y n ω (τ i)) atTop
        (fun ω i => v ω (τ i)) (fun _ => P) P' := by
    let f (z : Fin m → E) (i : Fin m) := unweight (τ i) • z i
    have hf : Continuous f := continuous_pi (fun i =>
      (show Continuous (fun p : Fin m → E => p i) from continuous_apply i).const_smul
        (unweight (τ i)))
    have hh := (hUL m (fun i => time (τ i))).continuous_comp hf
    have he (n : ℕ) (ω : Ω) (i : Fin m) :
        unweight (τ i) • Z (r n) ω (time (τ i)) = Y n ω (τ i) :=
      compactify_inverse _ (hτ i)
    exact hh.congr (fun n => Eventually.of_forall fun ω => funext (he n ω)) EventuallyEq.rfl
  have hYc (n : ℕ) (ω : Ω) (i : Fin k) : IsCadlag (fun t => Y n ω t i) := by
    have h0 := hX (r n) ω i
    constructor
    · intro t ht
      have h1 : Tendsto (fun s => X (r n) ω s i) (𝓝[Ici t] t) (𝓝 (X (r n) ω t i)) := h0.1 t ht
      exact Real.continuous_arctan.continuousAt.tendsto.comp h1
    · intro t ht
      obtain ⟨l,hl⟩ := h0.2 t ht
      exact ⟨Real.arctan l,Real.continuous_arctan.continuousAt.tendsto.comp hl⟩
  have hYm (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : Measurable (fun ω => Y n ω t) :=
    continuous_arctanVector.measurable.comp (hXm (r n) t ht)
  have hYM (T : ℕ) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
      ∃ δ > 0, ∀ᶠ n in atTop,
        P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
          ε ≤ ‖Y n ω s-Y n ω t‖} ≤ ENNReal.ofReal η := by
    obtain ⟨δ,hδ,hN⟩ := hM T ε η hε hη
    refine ⟨δ,hδ,?_⟩
    filter_upwards [hr.tendsto_atTop.eventually hN] with n hn
    refine (measure_mono ?_).trans hn
    rintro ω ⟨s,hs,t,ht,hst,hb⟩
    exact ⟨s,hs,t,ht,hst,hb.trans (arctanVector_lip _ _)⟩
  have hCouple := functional_coupling_from_fdd_and_interval_modulus Y v hYc hYm
    (fun ω => (hvc ω).continuousOn) (fun t _ => hvm t) hF hYM
  have hvSafe : ∀ᵐ ω ∂P', marginSafe (fun t : ℝ≥0 => v ω t) := by
    have hBound (T : ℕ) (η : ℝ) (hη : 0 < η) :
        ∃ A ≥ (0:ℝ), ∀ᶠ n in atTop,
          P {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), A < ‖X (r n) ω t‖} ≤ ENNReal.ofReal η := by
      obtain ⟨A,hA,hN⟩ := hB T η hη
      exact ⟨A,hA,hr.tendsto_atTop.eventually hN⟩
    have hh := arctangent_fdd_limit_is_interior_on_compact_rational_times (fun n => X (r n)) v hF hBound
    filter_upwards [hh] with ω hw
    intro T i
    obtain ⟨b,hb⟩ := hw T i
    exact ⟨b,fun q hq => by
      change |v ω ((q:ℝ).toNNReal:ℝ) i| ≤ _
      rw [Real.coe_toNNReal _ hq.1]
      exact hb q hq⟩
  let x (ω : Λ) (t : ℝ) (i : Fin k) :=
    if marginSafe (fun u : ℝ≥0 => v ω u) then Real.tan (v ω t i) else 0
  have hSafe (ω : Λ) (hω : marginSafe (fun t : ℝ≥0 => v ω t))
      (t : ℝ) (ht : 0 ≤ t) (i : Fin k) : v ω t i ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    obtain ⟨T,hT⟩ := exists_nat_gt t
    have hc (j : Fin k) (u : ℝ) (_ : 0 ≤ u) :
        ContinuousWithinAt (fun s => v ω s j) (Ici u) u :=
      ((continuous_apply j).comp (hvc ω)).continuousWithinAt
    obtain ⟨A,hA,hA',hBound⟩ := extend_margin hω hc T i
    have hi := abs_le.1 (hBound t ⟨ht,hT.le⟩)
    exact ⟨by linarith [hi.1],by linarith [hi.2]⟩
  have hxc (ω : Λ) : ContinuousOn (x ω) (Ici (0:ℝ)) := by
    by_cases hω : marginSafe (fun t : ℝ≥0 => v ω t)
    · intro t ht
      apply continuousWithinAt_pi.2
      intro i
      simp only [x,if_pos hω]
      exact (Real.continuousAt_tan.2 (Real.cos_pos_of_mem_Ioo (hSafe ω hω t ht i)).ne').tendsto.comp
        (((continuous_apply i).comp (hvc ω)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    · simp only [x,if_neg hω]
      exact continuousOn_const
  have hxm (t : ℝ) (ht : 0 ≤ t) : Measurable (fun ω => x ω t) := by
    let t' : ℝ≥0 := ⟨t,ht⟩
    have hp : Measurable (fun ω (s : ℝ≥0) => v ω s) :=
      measurable_pi_lambda _ (fun s => hvm s)
    have h := ((measurable_pi_apply t').comp tangent_decode_measurable).comp hp
    exact h
  have hId : (fun ω (t : ℝ≥0) => v ω t) =ᵐ[P'] (fun ω (t : ℝ≥0) i => Real.arctan (x ω t i)) := by
    filter_upwards [hvSafe] with ω hw
    funext t i
    simp only [x,if_pos hw]
    have hI := hSafe ω hw t t.2 i
    exact (Real.arctan_tan hI.1 hI.2).symm
  have hxD (ω : Λ) (i : Fin k) : IsCadlag (fun t => x ω t i) := by
    have h := (continuous_apply i).comp_continuousOn (hxc ω)
    constructor
    · intro t ht
      exact (h t ht).mono (Ici_subset_Ici.2 ht)
    · intro t ht
      refine ⟨x ω t i,(h t ht.le).mono_left ?_⟩
      apply le_inf nhdsWithin_le_nhds
      rw [le_principal_iff]
      exact mem_nhdsWithin_of_mem_nhds (mem_of_superset (Ioi_mem_nhds ht) Ioi_subset_Ici_self)
  refine ⟨r,hr,Λ,inferInstance,P',x,inferInstance,hxc,hxm,?_⟩
  apply arctangent_path_coupling_recovers_original_paths P P' (fun n => X (r n)) x
    (fun n => hX (r n)) hxD
  obtain ⟨Ω₀,m₀,P₀,U,w,hP₀,hU,hw,hCd,hCv⟩ := hCouple
  letI := m₀
  exact ⟨Ω₀,m₀,P₀,U,w,hP₀,hU,hw.trans (IdentDistrib.of_ae_eq hw.aemeasurable_snd hId),hCd,hCv⟩
