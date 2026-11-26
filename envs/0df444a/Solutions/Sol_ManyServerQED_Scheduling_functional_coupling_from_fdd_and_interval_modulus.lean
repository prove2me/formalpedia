-- Prove2me | solution 1 for ManyServerQED.Scheduling.functional_coupling_from_fdd_and_interval_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:06:38.305801+00:00
-- url     : https://prove2.me/submissions/dfafd81e-2956-4e4a-901e-c28b117de564

import Theorems.Thm_Reiman84_QueueLength_weakConvD_of_fdd_and_modulus
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

private theorem compactify_tendsto_one {k : ℕ} (f : ℝ → Fin k → ℝ) {S : Set ℝ}
    (hS : S ⊆ Iic (1:ℝ)) : Tendsto (compactify f) (𝓝[S] 1) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hW : Tendsto (fun s : ℝ => (1-s)*(Real.pi/2)) (𝓝[S] 1) (𝓝 0) := by
    have hV : Continuous (fun s : ℝ => (1-s)*(Real.pi/2)) := by fun_prop
    have hc : Tendsto (fun s : ℝ => (1-s)*(Real.pi/2)) (𝓝[S] 1) (𝓝 ((1-1)*(Real.pi/2))) :=
      hV.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [sub_self,zero_mul] using hc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hW
    (Eventually.of_forall fun _ => norm_nonneg _) (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact norm_compactify f (hS hs))

private theorem compactify_cadlag_path {k : ℕ} {f : ℝ → Fin k → ℝ}
    (hf : ∀ i, IsCadlag (fun t => f t i)) : IsCadlag01 (compactify f) := by
  constructor
  · intro s hs
    have hS : Tendsto compressedTime (𝓝[Icc s 1] s) (𝓝[Ici (compressedTime s)] (compressedTime s)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (continuousAt_compressedTime hs.2).tendsto.mono_left nhdsWithin_le_nhds
      · have hLt : Iio (1:ℝ) ∈ 𝓝[Icc s 1] s :=
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs.2)
        filter_upwards [self_mem_nhdsWithin,hLt] with t ht ht'
        change compressedTime s ≤ compressedTime t
        rcases ht.1.eq_or_lt with h | h
        · rw [h]
        · exact (compressedTime_mono hs ⟨hs.1.trans ht.1,ht'⟩ h).le
    have hU : Tendsto f (𝓝[Ici (compressedTime s)] (compressedTime s)) (𝓝 (f (compressedTime s))) := by
      apply tendsto_pi_nhds.2
      intro i
      exact (hf i).1 _ (compressedTime_nonneg ⟨hs.1,hs.2.le⟩)
    exact (continuous_timeLeft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).smul
      (continuous_arctanVector.continuousAt.tendsto.comp (hU.comp hS))
  · intro s hs
    rcases hs.2.lt_or_eq with hb | rfl
    · have hC : 0 < compressedTime s := div_pos hs.1 (sub_pos.2 hb)
      have hS : Tendsto compressedTime (𝓝[Ico 0 s] s) (𝓝[<] (compressedTime s)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact (continuousAt_compressedTime hb).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          exact compressedTime_mono ⟨ht.1,ht.2.trans hb⟩ ⟨hs.1.le,hb⟩ ht.2
      choose l hl using fun i => (hf i).2 _ hC
      have hF : Tendsto f (𝓝[<] (compressedTime s)) (𝓝 l) := tendsto_pi_nhds.2 hl
      exact ⟨timeLeft s • arctanVector l,
        (continuous_timeLeft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).smul
          (continuous_arctanVector.continuousAt.tendsto.comp (hF.comp hS))⟩
    · exact ⟨0,compactify_tendsto_one _ (fun _ h => h.2.le)⟩

set_option maxHeartbeats 1000000 in
private theorem compactified_path_regularity {k : ℕ} (f : ℝ → Fin k → ℝ) :
    let z (s : ℝ) := max 0 (1-s) • (fun i => Real.arctan (f (s/(1-s)) i))
    ((∀ i, IsCadlag (fun t => f t i)) → IsCadlag01 z) ∧
    (ContinuousOn f (Set.Ici 0) → ContinuousOn z (Set.Icc (0:ℝ) 1)) := by
  intro z
  change ((∀ i, IsCadlag (fun t => f t i)) → IsCadlag01 (compactify f)) ∧
    (ContinuousOn f (Set.Ici 0) → ContinuousOn (compactify f) (Set.Icc (0:ℝ) 1))
  refine ⟨compactify_cadlag_path,?_⟩
  intro hF s hs
  rcases hs.2.lt_or_eq with hb | rfl
  · have hS : ContinuousWithinAt compressedTime (Icc (0:ℝ) 1) s :=
      (continuousAt_compressedTime hb).continuousWithinAt
    have hf := (hF _ (compressedTime_nonneg hs)).comp hS
      (fun t ht => compressedTime_nonneg ht)
    exact continuous_timeLeft.continuousWithinAt.smul
      (continuous_arctanVector.continuousAt.comp_continuousWithinAt hf)
  · rw [ContinuousWithinAt,compactify_one]
    exact compactify_tendsto_one _ (fun _ h => h.2)

private theorem compactified_diff_le {k : ℕ} (x : ℝ → Fin k → ℝ) {s t : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖compactify x s-compactify x t‖ ≤ ‖x (compressedTime s)-x (compressedTime t)‖
      + |s-t| *(Real.pi/2) := by
  let u := arctanVector (x (compressedTime s))
  let v := arctanVector (x (compressedTime t))
  rw [compactify, compactify,timeLeft_eq hs.2,timeLeft_eq ht.2]
  change ‖(1-s) • u-(1-t) • v‖ ≤ _
  have he : (1-s) • u-(1-t) • v = (1-s) • (u-v)+(t-s) • v := by
    module
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_sub_comm t s,
    abs_of_nonneg (sub_nonneg.2 hs.2)]
  apply add_le_add
  · exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hs.1])).trans
      (arctanVector_lip _ _)
  · exact mul_le_mul_of_nonneg_left (norm_arctanVector _) (abs_nonneg _)

private theorem compactified_path_modulus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (X : ℕ → Ω → ℝ → Fin k → ℝ)
    (h : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    let z (n : ℕ) (ω : Ω) (s : ℝ) := max 0 (1-s) • (fun i => Real.arctan (X n ω (s/(1-s)) i))
    ∀ (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1, |s-t| ≤ δ ∧
        ε ≤ ‖z n ω s-z n ω t‖} ≤ ENNReal.ofReal η := by
  intro z ε η hε hη
  let C := Real.pi/2
  have hC : 0 < C := by dsimp [C]; positivity
  let a := min (1/4) (ε/(16*(C+1)))
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha' : a ≤ 1/4 := min_le_left _ _
  have hsmall : 4*a*C < ε := by
    have h0 := (le_div_iff₀ (show 0 < 16*(C+1) by positivity)).1 (min_le_right (1/4:ℝ) (ε/(16*(C+1))))
    nlinarith [mul_pos ha hC,hε]
  obtain ⟨T,hT⟩ := exists_nat_gt (1/a)
  obtain ⟨d,hd,hN⟩ := h T (ε/2) η (by positivity) hη
  let δ := min a (d*a*a)
  have hδ : 0 < δ := lt_min ha (by positivity)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hN] with n hn
  refine (measure_mono ?_).trans hn
  rintro ω ⟨s,hs,t,ht,hst,hBad⟩
  have hx : z n ω = compactify (X n ω) := rfl
  rw [hx] at hBad
  have hδa : |s-t| ≤ a := hst.trans (min_le_left _ _)
  have hδd : |s-t| ≤ d*a*a := hst.trans (min_le_right _ _)
  have hClose : 1-a ≤ s ∨ 1-a ≤ t → False := by
    intro hST
    have hab := abs_le.1 hδa
    have hsA : 1-2*a ≤ s := by rcases hST with h | h <;> linarith
    have htA : 1-2*a ≤ t := by rcases hST with h | h <;> linarith
    have hDiff := (norm_sub_le (compactify (X n ω) s) _).trans
      (add_le_add (norm_compactify (X n ω) hs.2) (norm_compactify (X n ω) ht.2))
    change ‖compactify (X n ω) s-compactify (X n ω) t‖ ≤ (1-s)*C+(1-t)*C at hDiff
    have hsN : (1-s)*C ≤ 2*a*C :=
      mul_le_mul_of_nonneg_right (by linarith) hC.le
    have htN : (1-t)*C ≤ 2*a*C :=
      mul_le_mul_of_nonneg_right (by linarith) hC.le
    linarith only [hBad,hDiff,hsN,htN,hsmall]
  have hsD : a ≤ 1-s := by linarith [lt_of_not_ge (fun h => hClose (Or.inl h))]
  have htD : a ≤ 1-t := by linarith [lt_of_not_ge (fun h => hClose (Or.inr h))]
  have hsP : 0 < 1-s := ha.trans_le hsD
  have htP : 0 < 1-t := ha.trans_le htD
  have hTime (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) (hrA : a ≤ 1-r) :
      compressedTime r ∈ Icc (0:ℝ) (T:ℝ) := by
    refine ⟨compressedTime_nonneg hr,(le_trans ?_ hT.le)⟩
    unfold compressedTime
    exact (div_le_div_of_nonneg_right hr.2 ((ha.trans_le hrA).le)).trans
      (div_le_div_of_nonneg_left zero_le_one ha hrA)
  have hDen : a*a ≤ (1-s)*(1-t) := mul_le_mul hsD htD ha.le hsP.le
  have hAlgo : compressedTime s-compressedTime t = (s-t)/((1-s)*(1-t)) := by
    unfold compressedTime
    field_simp [hsP.ne',htP.ne']
    ring
  refine ⟨compressedTime s,hTime s hs hsD,compressedTime t,hTime t ht htD,?_,?_⟩
  · rw [hAlgo,abs_div,abs_of_pos (mul_pos hsP htP)]
    exact (div_le_iff₀ (mul_pos hsP htP)).2
      (hδd.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hDen hd.le))
  · have hEst := compactified_diff_le (X n ω) hs ht
    have hErr : |s-t| *C ≤ a*C := mul_le_mul_of_nonneg_right hδa hC.le
    change ‖compactify (X n ω) s-compactify (X n ω) t‖ ≤
      ‖X n ω (compressedTime s)-X n ω (compressedTime t)‖+|s-t| *C at hEst
    linarith only [hEst,hErr,hBad,hsmall,mul_pos ha hC,hε]
private theorem cadlag_compact_bounds (f : ℝ → ℝ) (hf : IsCadlag f) (T : ℝ) :
    ∃ C ≥ (0:ℝ), ∀ t ∈ Set.Icc (0:ℝ) T, |f t| ≤ C := by
  have hl (s : ℝ) (hs : s ∈ Icc (0:ℝ) T) :
      ∃ r > (0:ℝ), ∃ C ≥ (0:ℝ), ∀ t ∈ Metric.ball s r ∩ Icc (0:ℝ) T, |f t| ≤ C := by
    obtain ⟨r,hr,hright⟩ := Metric.continuousWithinAt_iff.1 (hf.1 s hs.1) 1 zero_lt_one
    rcases hs.1.eq_or_lt with h | h
    · refine ⟨r,hr,|f s|+1,by positivity,?_⟩
      intro t ht
      have hts : s ≤ t := h ▸ ht.2.1
      have hft := hright hts ht.1
      rw [Real.dist_eq] at hft
      have w := abs_add_le (f t-f s) (f s)
      rw [sub_add_cancel] at w
      linarith
    · obtain ⟨u,hu⟩ := hf.2 s h
      have hleft := (Metric.tendsto_nhdsWithin_nhds.1 hu) 1 zero_lt_one
      obtain ⟨q,hq,hq'⟩ := hleft
      refine ⟨min r q,lt_min hr hq,max |f s| |u|+1,by positivity,?_⟩
      intro t ht
      have ht' : dist t s < min r q := ht.1
      rcases le_or_gt s t with hst | hst
      · have hft := hright hst (lt_min_iff.1 ht').1
        rw [Real.dist_eq] at hft
        have w := abs_add_le (f t-f s) (f s)
        rw [sub_add_cancel] at w
        linarith [le_max_left |f s| |u|]
      · have hft := hq' hst (lt_min_iff.1 ht').2
        rw [Real.dist_eq] at hft
        have w := abs_add_le (f t-u) u
        rw [sub_add_cancel] at w
        linarith [le_max_right |f s| |u|]
  choose r hr C hC h using fun s : Icc (0:ℝ) T => hl s s.2
  obtain ⟨S,hS⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).elim_finite_subcover
    (fun s : Icc (0:ℝ) T => Metric.ball (s:ℝ) (r s))
    (fun _ => Metric.isOpen_ball) (by
      intro s hs
      exact mem_iUnion.2 ⟨⟨s,hs⟩,Metric.mem_ball_self (hr ⟨s,hs⟩)⟩)
  refine ⟨∑ s ∈ S,C s,Finset.sum_nonneg (fun s _ => hC s),?_⟩
  intro t ht
  obtain ⟨s,hs,hst⟩ := mem_iUnion₂.1 (hS ht)
  exact (h s t ⟨hst,ht⟩).trans (Finset.single_le_sum (fun s _ => hC s) hs)

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

private theorem arctan_margin {k : ℕ} (x : ℝ → Fin k → ℝ)
    (hx : ∀ i, IsCadlag (fun t => x t i)) :
    marginSafe (fun t : ℝ≥0 => fun i => Real.arctan (x t i)) := by
  intro T i
  obtain ⟨C,hC,hD⟩ := cadlag_compact_bounds (fun t => x t i) (hx i) (T:ℝ)
  have hε : 0 < Real.pi/2 - Real.arctan C := sub_pos.2 (Real.arctan_lt_pi_div_two _)
  obtain ⟨b,hb⟩ := exists_nat_gt (1/(Real.pi/2-Real.arctan C))
  refine ⟨b,fun q hq => ?_⟩
  have hsm : 1/((b:ℝ)+1) < Real.pi/2-Real.arctan C := by
    apply (div_lt_iff₀ (by positivity : 0 < (b:ℝ)+1)).2
    have h := (div_lt_iff₀ hε).1 hb
    nlinarith
  have hxy := abs_le.1 (hD q hq)
  have h1 := Real.arctan_mono hxy.1
  have h2 := Real.arctan_mono hxy.2
  rw [Real.arctan_neg] at h1
  change |Real.arctan (x ((q:ℝ).toNNReal:ℝ) i)| ≤ _
  rw [Real.coe_toNNReal _ hq.1]
  exact (abs_le.2 ⟨h1,h2⟩).trans (by linarith)

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

private theorem tangent_cadlag {k : ℕ} (y : ℝ → Fin k → ℝ)
    (hy : ∀ i, IsCadlag (fun t => y t i)) (h : marginSafe (fun t : ℝ≥0 => y t))
    (i : Fin k) : IsCadlag (fun t => Real.tan (y t i)) := by
  have hRight := fun (j : Fin k) => (hy j).1
  constructor
  · intro t ht
    obtain ⟨T,hT⟩ := exists_nat_gt t
    obtain ⟨C,hC,hCl,hCb⟩ := extend_margin h hRight T i
    have hI := abs_le.1 (hCb t ⟨ht,hT.le⟩)
    have hct : ContinuousAt Real.tan (y t i) :=
      Real.continuousAt_tan.2 (Real.cos_pos_of_mem_Ioo ⟨by linarith,by linarith⟩).ne'
    have hh : Tendsto (fun s : ℝ => y s i) (𝓝[Ici t] t) (𝓝 (y t i)) := (hy i).1 t ht
    exact hct.tendsto.comp hh
  · intro t ht
    obtain ⟨l,hl⟩ := (hy i).2 t ht
    obtain ⟨T,hT⟩ := exists_nat_gt t
    obtain ⟨C,hC,hCl,hCb⟩ := extend_margin h hRight T i
    have hEvent : ∀ᶠ s in 𝓝[<] t, y s i ∈ Icc (-C) C := by
      have hh : Ioo (0:ℝ) T ∈ 𝓝[<] t :=
        mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ht hT)
      filter_upwards [hh] with s hs
      exact abs_le.1 (hCb s ⟨hs.1.le,hs.2.le⟩)
    have hi : l ∈ Icc (-C) C := isClosed_Icc.mem_of_tendsto hl hEvent
    have hc : ContinuousAt Real.tan l :=
      Real.continuousAt_tan.2 (Real.cos_pos_of_mem_Ioo ⟨by linarith [hi.1],by linarith [hi.2]⟩).ne'
    exact ⟨Real.tan l,hc.tendsto.comp hl⟩

private theorem projections_uoc {k : ℕ} {u : ℕ → ℝ → Fin k → ℝ} {v : ℝ → Fin k → ℝ} {T : ℝ}
    (h : Tendsto (fun n => supDist (u n) v T) atTop (𝓝 0)) (i : Fin k) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) T, |u n t i-v t i| < ε := by
  filter_upwards [(tendsto_order.1 h).2 _ (ENNReal.ofReal_pos.2 he)] with n hn
  intro t ht
  have hsum : |u n t i-v t i| ≤ ∑ j, |u n t j-v t j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (u n t j-v t j)) (Finset.mem_univ _)
  have hb : ENNReal.ofReal |u n t i-v t i| ≤ supDist (u n) v T :=
    (ENNReal.ofReal_le_ofReal hsum).trans (le_iSup_of_le t (le_iSup_of_le ht le_rfl))
  exact (ENNReal.ofReal_lt_ofReal_iff he).1 (hb.trans_lt hn)

private theorem right_limit_of_uoc {k : ℕ} {u : ℕ → ℝ → Fin k → ℝ} {v : ℝ → Fin k → ℝ}
    (hu : ∀ n i, IsCadlag (fun t => u n t i))
    (h : ∀ T, 0 ≤ T → Tendsto (fun n => supDist (u n) v T) atTop (𝓝 0))
    (i : Fin k) (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (fun s => v s i) (Ici t) t := by
  apply Metric.continuousWithinAt_iff.2
  intro ε he
  obtain ⟨n,hn⟩ := (projections_uoc (h (t+1) (by linarith)) i (ε/3) (by positivity)).exists
  obtain ⟨δ,hδ,hW⟩ := Metric.continuousWithinAt_iff.1 ((hu n i).1 t ht) (ε/3) (by positivity)
  refine ⟨min δ 1,lt_min hδ zero_lt_one,?_⟩
  intro s hs hst
  have hD : dist s t < 1 := (lt_min_iff.1 hst).2
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.2 hs)] at hD
  have h1 := hn s ⟨ht.trans hs,by linarith⟩
  have h2 := hn t ⟨ht,by linarith⟩
  have h3 := hW hs (lt_min_iff.1 hst).1
  rw [Real.dist_eq] at h3 ⊢
  have d1 := abs_sub_le (v s i) (u n s i) (v t i)
  have d2 := abs_sub_le (u n s i) (u n t i) (v t i)
  rw [abs_sub_comm (v s i) (u n s i)] at d1
  linarith only [h1,h2,h3,d1,d2]

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

private theorem recover_margin_law {Λ Ξ : Type*} [MeasurableSpace Λ] [MeasurableSpace Ξ] {k : ℕ} {Q : Measure Λ} {p : Λ → ℝ≥0 → Fin k → ℝ}
      {U : Ξ → ℝ → Fin k → ℝ} {R : Measure Ξ}
      (hl : IdentDistrib p (fun ω (t : ℝ≥0) i => Real.arctan (U ω t i)) Q R)
      (hU : ∀ ω i, IsCadlag (fun t => U ω t i)) :
      (∀ᵐ ω ∂Q, marginSafe (p ω)) ∧ IdentDistrib (tangent_decode ∘ p)
        (fun ω (t : ℝ≥0) => U ω t) Q R := by
    have hG (ω : Ξ) := arctan_margin (U ω) (hU ω)
    have hI := hl.comp tangent_decode_measurable
    refine ⟨?_,?_⟩
    · have eq : Q {ω | ¬marginSafe (p ω)} = R {ω | ¬marginSafe
          (fun t : ℝ≥0 => fun i => Real.arctan (U ω t i))} := by
        let B : Set (ℝ≥0 → Fin k → ℝ) := {p | marginSafe p}
        have hB : MeasurableSet Bᶜ := margin_measurable.compl
        have HH := congrArg (fun M : Measure (ℝ≥0 → Fin k → ℝ) => M Bᶜ) hl.map_eq
        rwa [Measure.map_apply_of_aemeasurable hl.aemeasurable_fst hB,
          Measure.map_apply_of_aemeasurable hl.aemeasurable_snd hB] at HH
      apply ae_iff.2
      rw [eq]
      simp [hG]
    · have e : (tangent_decode ∘ fun ω (t : ℝ≥0) (i : Fin k) => Real.arctan (U ω t i)) =
          (fun ω (t : ℝ≥0) => U ω t) := by
        funext ω t i
        simp only [Function.comp_def,tangent_decode,if_pos (hG ω),Real.tan_arctan]
      rw [e] at hI
      exact hI

set_option maxHeartbeats 1700000 in
private theorem arctan_coupling_recovery {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (P : Measure Ω) (P' : Measure Ω')
    (X : ℕ → Ω → ℝ → Fin k → ℝ) (Z : Ω' → ℝ → Fin k → ℝ)
    (hX : ∀ n ω i, IsCadlag (fun t => X n ω t i))
    (hZ : ∀ ω i, IsCadlag (fun t => Z ω t i))
    (h : CouplingConverges P P'
      (fun n ω t i => Real.arctan (X n ω t i))
      (fun ω t i => Real.arctan (Z ω t i))) :
    CouplingConverges P P' X Z := by
  classical
  obtain ⟨Λ,mΛ,Q,Y,z,hQ,hY,hz,hcad,hC⟩ := h
  letI := mΛ
  let Yi (n : ℕ) (ω : Λ) (t : ℝ) (i : Fin k) :=
    if marginSafe (fun u : ℝ≥0 => Y n ω u) then Real.tan (Y n ω t i) else 0
  let zi (ω : Λ) (t : ℝ) (i : Fin k) :=
    if marginSafe (fun u : ℝ≥0 => z ω u) then Real.tan (z ω t i) else 0
  have hevent : ∀ᶠ n in atTop, ∀ᵐ ω ∂Q, marginSafe (fun u : ℝ≥0 => Y n ω u) :=
    hY.mono (fun n hn => (recover_margin_law (p := fun ω (t : ℝ≥0) => Y n ω t) (U := X n) (R := P) hn (hX n)).1)
  have hSafe : ∀ᵐ ω ∂Q, ∀ᶠ n in atTop, marginSafe (fun u : ℝ≥0 => Y n ω u) := by
    obtain ⟨N,hN⟩ := eventually_atTop.1 hevent
    have h : ∀ᵐ ω ∂Q, ∀ n : ℕ, N ≤ n → marginSafe (fun u : ℝ≥0 => Y n ω u) :=
      ae_all_iff.2 (fun n => by by_cases hn : N ≤ n <;> simp [hn,hN])
    exact h.mono (fun _ hw => eventually_atTop.2 ⟨N,hw⟩)
  have hzS := recover_margin_law (p := fun ω (t : ℝ≥0) => z ω t) (U := Z) (R := P') hz hZ
  refine ⟨Λ,mΛ,Q,Yi,zi,hQ,hY.mono (fun n hn => (recover_margin_law (p := fun ω (t : ℝ≥0) => Y n ω t) (U := X n) (R := P) hn (hX n)).2),hzS.2,?_,?_⟩
  · intro n ω i
    by_cases hG : marginSafe (fun t : ℝ≥0 => Y n ω t)
    · simpa only [Yi,if_pos hG] using tangent_cadlag (Y n ω) (hcad n ω) hG i
    · simpa only [Yi,if_neg hG] using
        (show IsCadlag (fun _ : ℝ => (0:ℝ)) from ⟨fun _ _ => continuousWithinAt_const,
          fun _ _ => ⟨0,tendsto_const_nhds⟩⟩)
  · filter_upwards [hC,hSafe,hzS.1] with ω hω hYω hzω
    intro T hT
    apply ENNReal.tendsto_nhds_zero.2
    intro η hη
    obtain ⟨ε,_,hε,hεη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
    have hε0 := ENNReal.ofReal_pos.1 hε
    let e := ε/(2*((k:ℝ)+1))
    have he : 0 < e := by dsimp [e]; positivity
    obtain ⟨N,hN⟩ := exists_nat_gt T
    have hNearly (i : Fin k) : ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) T,
        |Real.tan (Y n ω t i)-Real.tan (z ω t i)| < e := by
      obtain ⟨C,hC,hC',hCZ⟩ := extend_margin hzω
        (right_limit_of_uoc (fun n j => hcad n ω j) hω) N i
      let D := (C+Real.pi/2)/2
      have hCD : C < D := by dsimp [D]; linarith
      have hD : D < Real.pi/2 := by dsimp [D]; linarith
      have htan : ContinuousOn Real.tan (Icc (-D) D) := by
        intro v hv
        exact (Real.continuousAt_tan.2 (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [hv.1],by linarith [hv.2]⟩).ne').continuousWithinAt
      obtain ⟨δ,hδ,hU⟩ := Metric.uniformContinuousOn_iff.1
        (isCompact_Icc.uniformContinuousOn_of_continuous htan) e he
      filter_upwards [projections_uoc (hω T hT) i (min δ (D-C)) (lt_min hδ (sub_pos.2 hCD))]
        with n hn t ht
      have hz0 := hCZ t ⟨ht.1,ht.2.trans hN.le⟩
      have hh := hn t ht
      have hy0 : |Y n ω t i| ≤ D := by
        have hh' := (lt_min_iff.1 hh).2
        have htri := abs_add_le (Y n ω t i-z ω t i) (z ω t i)
        rw [sub_add_cancel] at htri
        linarith
      have hh' : dist (Y n ω t i) (z ω t i) < δ := by
        rw [Real.dist_eq]
        exact (lt_min_iff.1 hh).1
      have hFin := hU _ (abs_le.1 hy0) _ (abs_le.1 (hz0.trans hCD.le)) hh'
      simpa only [Real.dist_eq] using hFin
    filter_upwards [Filter.eventually_all.2 hNearly,hYω] with n hn hy
    have hbound : supDist (Yi n ω) (zi ω) T ≤ ENNReal.ofReal ((k:ℝ)*e) := by
      apply iSup_le
      intro t
      apply iSup_le
      intro ht
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ∑ _i : Fin k, e := Finset.sum_le_sum (fun i _ => by
          simpa only [Yi,zi,if_pos hy,if_pos hzω] using (hn i t ht).le)
        _ = _ := by simp
    refine hbound.trans ((ENNReal.ofReal_le_ofReal ?_).trans hεη.le)
    dsimp [e]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*((k:ℝ)+1))).2
    nlinarith

private theorem path_law_modulus_transfer {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} {P' : Measure Ω'}
    (X : Ω → ℝ → E) (Y : Ω' → ℝ → E)
    (hLaw : IdentDistrib (fun ω (t : ℝ≥0) => X ω t) (fun ω (t : ℝ≥0) => Y ω t) P P')
    (hX : ∀ ω s, 0 ≤ s → ContinuousWithinAt (X ω) (Ici s) s)
    (T : ℕ) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
      |s-t| ≤ δ ∧ ε ≤ dist (X ω s) (X ω t)} ≤
    P' {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
      |s-t| ≤ 2*δ ∧ ε/2 ≤ dist (Y ω s) (Y ω t)} := by
  let B : Set (ℝ≥0 → E) := {f | ∃ (q r : ℚ), (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧
    (r:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ |(q:ℝ)-(r:ℝ)| < 2*δ ∧
    ε/2 < dist (f (q:ℝ).toNNReal) (f (r:ℝ).toNNReal)}
  have hB : MeasurableSet B := by
    have he : B = ⋃ q : ℚ, ⋃ r : ℚ, {f | (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧
        (r:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ |(q:ℝ)-(r:ℝ)| < 2*δ ∧
        ε/2 < dist (f (q:ℝ).toNNReal) (f (r:ℝ).toNNReal)} := by ext; simp [B]
    rw [he]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun r => ?_
    by_cases c : (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ (r:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧
        |(q:ℝ)-(r:ℝ)| < 2*δ
    · simpa only [c.1,c.2.1,c.2.2,true_and] using
        (measurableSet_lt (measurable_const (a := ε/2))
          ((measurable_pi_apply (q:ℝ).toNNReal).dist (measurable_pi_apply (r:ℝ).toNNReal)) :
          MeasurableSet {f : ℝ≥0 → E | ε/2 < dist (f (q:ℝ).toNNReal) (f (r:ℝ).toNNReal)})
    · have hf : {f : ℝ≥0 → E | (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧
          (r:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ |(q:ℝ)-(r:ℝ)| < 2*δ ∧
          ε/2 < dist (f (q:ℝ).toNNReal) (f (r:ℝ).toNNReal)} = ∅ := by
        ext f
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
        exact fun h => c ⟨h.1,h.2.1,h.2.2.1⟩
      rw [hf]
      exact MeasurableSet.empty
  let F (ω : Ω) (t : ℝ≥0) := X ω t
  let G (ω : Ω') (t : ℝ≥0) := Y ω t
  have hMeasure : P (F ⁻¹' B) = P' (G ⁻¹' B) := by
    rw [← Measure.map_apply_of_aemeasurable hLaw.aemeasurable_fst hB,
      ← Measure.map_apply_of_aemeasurable hLaw.aemeasurable_snd hB]
    exact congrArg (fun m : Measure (ℝ≥0 → E) => m B) hLaw.map_eq
  calc
    _ ≤ P (F ⁻¹' B) := by
      apply measure_mono
      rintro ω ⟨s,hs,t,ht,hst,hval⟩
      let e := min (δ/4) (ε/8)
      have he : 0 < e := lt_min (by positivity) (by positivity)
      obtain ⟨q,hq,hqs,hQ⟩ := rational_right_approximation (hX ω) hs he
      obtain ⟨r,hr,hrt,hR⟩ := rational_right_approximation (hX ω) ht he
      have hT : |(q:ℝ)-(r:ℝ)| < 2*δ := by
        have h1 := dist_triangle (q:ℝ) s (r:ℝ)
        have h2 := dist_triangle s t (r:ℝ)
        rw [dist_comm t (r:ℝ)] at h2
        rw [← Real.dist_eq] at hst ⊢
        have he' : e ≤ δ/4 := min_le_left _ _
        linarith only [h1,h2,hst,hqs,hrt,he',hδ]
      have hv : ε/2 < dist (X ω q) (X ω r) := by
        have h1 := dist_triangle (X ω s) (X ω q) (X ω t)
        have h2 := dist_triangle (X ω q) (X ω r) (X ω t)
        rw [dist_comm (X ω s) (X ω q)] at h1
        have he' : e ≤ ε/8 := min_le_right _ _
        linarith only [h1,h2,hval,hQ,hR,he',hε]
      refine ⟨q,r,hq,hr,hT,?_⟩
      simpa only [F,Real.coe_toNNReal _ hq.1,Real.coe_toNNReal _ hr.1] using hv
    _ = P' (G ⁻¹' B) := hMeasure
    _ ≤ _ := by
      apply measure_mono
      rintro ω ⟨q,r,hq,hr,hd,hv⟩
      refine ⟨q,hq,r,hr,hd.le,?_⟩
      simpa only [G,Real.coe_toNNReal _ hq.1,Real.coe_toNNReal _ hr.1] using hv.le

private theorem rational_near_cadlag {k : ℕ} {f : ℝ → Fin k → ℝ} (hf : IsCadlag01 f)
    {t ε : ℝ} (ht : t ∈ Icc 0 1) (hε : 0 < ε) :
    ∃ q : ℚ, (q:ℝ) ∈ Icc 0 1 ∧ dist (q:ℝ) t < ε ∧ dist (f q) (f t) < ε := by
  rcases ht.2.lt_or_eq with h | h
  · obtain ⟨δ, hδ, hV⟩ := Metric.continuousWithinAt_iff.mp (hf.1 t ⟨ht.1,h⟩) ε hε
    have hm : t < min 1 (t + min δ ε) :=
      lt_min h (lt_add_of_pos_right _ (lt_min hδ hε))
    obtain ⟨q, hq, hq'⟩ := exists_rat_btwn hm
    have hq1 : (q:ℝ) ≤ 1 := (lt_min_iff.mp hq').1.le
    have hd : dist (q:ℝ) t < min δ ε := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hq)]
      linarith [(lt_min_iff.mp hq').2]
    exact ⟨q, ⟨ht.1.trans hq.le, hq1⟩, (lt_min_iff.mp hd).2,
      hV ⟨hq.le, hq1⟩ (lt_min_iff.mp hd).1⟩
  · subst t
    exact ⟨1, by norm_num, by simpa using hε, by simpa using hε⟩

private def rational_uc {k : ℕ} (f : ℝ → Fin k → ℝ) : Prop :=
  ∀ m : ℕ, ∃ j : ℕ, ∀ u v : ℚ,
    (u:ℝ) ∈ Icc 0 1 → (v:ℝ) ∈ Icc 0 1 →
    dist (u:ℝ) (v:ℝ) < 1/((j:ℝ)+1) → dist (f u) (f v) ≤ 1/((m:ℝ)+1)

private theorem exists_small_reciprocal {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1/((m:ℝ)+1) < ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1/ε)
  refine ⟨m, (div_lt_iff₀ (by positivity)).2 ?_⟩
  have hh := (div_lt_iff₀ hε).1 hm
  nlinarith

private theorem cont_rational_uc {k : ℕ} {f : ℝ → Fin k → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    rational_uc f := by
  intro m
  obtain ⟨δ, hδ, hu⟩ := (Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf))
    (1/((m:ℝ)+1)) (by positivity)
  obtain ⟨j, hj⟩ := exists_small_reciprocal hδ
  exact ⟨j, fun u v hu0 hv0 huv => (hu _ hu0 _ hv0 (huv.trans hj)).le⟩

private theorem measurableSet_rational_uc {k : ℕ} :
    MeasurableSet {f : ℝ → Fin k → ℝ | rational_uc f} := by
  classical
  have hs : {f : ℝ → Fin k → ℝ | rational_uc f} = (⋂ m : ℕ, ⋃ j : ℕ, ⋂ u : ℚ, ⋂ v : ℚ,
      {f : ℝ → Fin k → ℝ | (u:ℝ) ∈ Icc 0 1 → (v:ℝ) ∈ Icc 0 1 →
        dist (u:ℝ) (v:ℝ) < 1/((j:ℝ)+1) → dist (f u) (f v) ≤ 1/((m:ℝ)+1)}) := by
    ext f
    simp [rational_uc]
  rw [hs]
  refine MeasurableSet.iInter (fun m => MeasurableSet.iUnion (fun j =>
    MeasurableSet.iInter (fun u => MeasurableSet.iInter (fun v => ?_))))
  by_cases h : (u:ℝ) ∈ Icc 0 1 ∧ (v:ℝ) ∈ Icc 0 1 ∧ dist (u:ℝ) (v:ℝ) < 1/((j:ℝ)+1)
  · simpa only [h.1, h.2.1, h.2.2, true_implies] using
      measurableSet_le ((measurable_pi_apply (u:ℝ)).dist (measurable_pi_apply (v:ℝ)))
        (measurable_const (a := 1 / ((m:ℝ)+1)))
  · have he : {f : ℝ → Fin k → ℝ | (u:ℝ) ∈ Icc 0 1 → (v:ℝ) ∈ Icc 0 1 →
      dist (u:ℝ) (v:ℝ) < 1/((j:ℝ)+1) → dist (f u) (f v) ≤ 1/((m:ℝ)+1)} = univ := by
      ext f
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact fun a b c => (h ⟨a,b,c⟩).elim
    rw [he]
    exact MeasurableSet.univ

private theorem rational_uc_to_uniform {k : ℕ} {f : ℝ → Fin k → ℝ}
    (hf : IsCadlag01 f) (hu : rational_uc f) : UniformContinuousOn f (Icc 0 1) := by
  apply Metric.uniformContinuousOn_iff.2
  intro ε hε
  obtain ⟨m, hm⟩ := exists_small_reciprocal (show 0 < ε/3 by positivity)
  obtain ⟨j, hj⟩ := hu m
  let δ : ℝ := 1/((j:ℝ)+1)/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, fun s hs t ht hst => ?_⟩
  have hsmall : 0 < min δ (ε/3) := lt_min hδ (by positivity)
  obtain ⟨u, hu, hus, hFus⟩ := rational_near_cadlag hf hs hsmall
  obtain ⟨v, hv, hvt, hFvt⟩ := rational_near_cadlag hf ht hsmall
  have huv : dist (u:ℝ) (v:ℝ) < 1/((j:ℝ)+1) := by
    have h₁ := dist_triangle (u:ℝ) s (v:ℝ)
    have h₂ := dist_triangle s t (v:ℝ)
    rw [dist_comm t (v:ℝ)] at h₂
    dsimp [δ] at hus hvt hst
    linarith [(lt_min_iff.mp hus).1,(lt_min_iff.mp hvt).1]
  have hmid := hj u v hu hv huv
  have h₁ := dist_triangle (f s) (f u) (f t)
  have h₂ := dist_triangle (f u) (f v) (f t)
  rw [dist_comm (f s) (f u)] at h₁
  linarith [(lt_min_iff.mp hFus).2,(lt_min_iff.mp hFvt).2]

private theorem sk_uniform {k : ℕ} {Y : ℕ → ℝ → Fin k → ℝ} {y : ℝ → Fin k → ℝ}
    (h : SkorohodTendsto Y y) (hy : UniformContinuousOn y (Icc 0 1)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ s ∈ Icc (0:ℝ) 1, ‖Y n s - y s‖ < ε := by
  obtain ⟨l, hl, hconv⟩ := h.2.2
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp hy (ε/2) (by positivity)
  filter_upwards [hconv (min δ (ε/2)) (lt_min hδ (by positivity))] with n hn
  intro s hs
  have him := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) (hl n).1
  rw [(hl n).2.2.1, (hl n).2.2.2] at him
  obtain ⟨r, hr, her⟩ := him hs
  have hn' := hn r hr
  rw [her] at hn'
  have hd : dist r s < δ := by
    rw [dist_comm, Real.dist_eq]
    exact (lt_min_iff.mp hn'.1).1
  have hU : ‖y r - y s‖ < ε/2 := by simpa only [dist_eq_norm] using hu r hr s hs hd
  have ht := norm_add_le (Y n s - y r) (y r - y s)
  rw [show Y n s - y r + (y r - y s) = Y n s - y s by abel] at ht
  linarith [(lt_min_iff.mp hn'.2).2, hU]

private theorem cadlag_of_pulled {k : ℕ} (z : ℝ → Fin k → ℝ) (hz : IsCadlag01 z)
    (c w : ℝ → ℝ) (hc : Continuous c) (hw : Continuous w) (hcm : StrictMonoOn c (Ici 0))
    (hc01 : ∀ t : ℝ, 0 ≤ t → c t ∈ Ico 0 1) (i : Fin k) :
    IsCadlag (fun t => w t * z (c t) i) := by
  constructor
  · intro t ht
    have hMap : MapsTo c (Ici t) (Icc (c t) 1) := by
      intro s hs
      have hs0 : 0 ≤ s := ht.trans hs
      exact ⟨hcm.monotoneOn ht hs0 hs, (hc01 s hs0).2.le⟩
    have hZ := (continuous_apply i).continuousAt.comp_continuousWithinAt
      ((hz.1 _ (hc01 t ht)).comp hc.continuousWithinAt hMap)
    exact hw.continuousWithinAt.mul hZ
  · intro t ht
    have hct : c t ∈ Ioc 0 1 := ⟨lt_of_le_of_lt (hc01 0 le_rfl).1
      (hcm (show (0:ℝ) ∈ Ici 0 from mem_Ici.2 le_rfl) (show t ∈ Ici 0 from ht.le) ht), (hc01 t ht.le).2.le⟩
    obtain ⟨l, hL⟩ := hz.2 (c t) hct
    have htc : Tendsto c (𝓝[<] t) (𝓝[Ico 0 (c t)] (c t)) := by
      apply tendsto_nhdsWithin_iff.2
      refine ⟨hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      have hu : ∀ᶠ s in 𝓝[<] t, s < t := self_mem_nhdsWithin
      have hpos : ∀ᶠ s in 𝓝[<] t, s ∈ Ioi (0:ℝ) :=
        nhdsWithin_le_nhds (Ioi_mem_nhds ht)
      filter_upwards [hu, hpos] with s hs hs0
      have hs0' : (0:ℝ) ≤ s := (mem_Ioi.1 hs0).le
      exact ⟨(hc01 s hs0').1, hcm (mem_Ici.2 hs0') (mem_Ici.2 ht.le) hs⟩
    have hQ := ((continuous_apply i).continuousAt.tendsto.comp hL).comp htc
    exact ⟨w t * l i, (hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul hQ⟩

private theorem map_map_meas_ae {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {f : α → β} {g : β → γ}
    (hg : Measurable g) (hf : AEMeasurable f μ) :
    (μ.map f).map g = μ.map (g ∘ f) := by
  ext s hs
  rw [Measure.map_apply hg hs, Measure.map_apply_of_aemeasurable hf (hg hs),
    Measure.map_apply_of_aemeasurable (hg.comp_aemeasurable hf) hs]
  rfl

set_option maxHeartbeats 1600000 in
private theorem coupled_unit_law_lift {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {k : ℕ}
    (P : Measure Ω) (P' : Measure Ω') (X : ℕ → Ω → ℝ → Fin k → ℝ)
    (x : Ω' → ℝ → Fin k → ℝ) (Z : ℕ → Ω → ℝ → Fin k → ℝ) (z : Ω' → ℝ → Fin k → ℝ)
    (c w : ℝ → ℝ) (hc : Continuous c) (hw : Continuous w)
    (hcm : StrictMonoOn c (Ici 0)) (hc01 : ∀ t : ℝ, 0 ≤ t → c t ∈ Ico 0 1)
    (hZeq : ∀ n ω t, 0 ≤ t → w t • Z n ω (c t) = X n ω t)
    (hzeq : ∀ ω t, 0 ≤ t → w t • z ω (c t) = x ω t)
    (hZ : ∀ n, AEMeasurable (fun ω => onUnit (Z n ω)) P)
    (hz : AEMeasurable (fun ω => onUnit (z ω)) P')
    (hzcont : ∀ ω, ContinuousOn (z ω) (Icc 0 1))
    (hweak : ∃ (Λ : Type) (_ : MeasurableSpace Λ) (Q : Measure Λ)
      (Y : ℕ → Λ → ℝ → Fin k → ℝ) (y : Λ → ℝ → Fin k → ℝ),
      IsProbabilityMeasure Q ∧ (∀ n, Measurable (Y n)) ∧ Measurable y ∧
      (∀ᶠ n in atTop, Q.map (Y n) = P.map (fun ω => onUnit (Z n ω))) ∧
      Q.map y = P'.map (fun ω => onUnit (z ω)) ∧
      ∀ᵐ ω ∂Q, SkorohodTendsto (fun n => Y n ω) (y ω)) :
    CouplingConverges P P' X x := by
  classical
  obtain ⟨Λ, mΛ, Q, Y, y, hQ, hY, hy, hmapY, hmapy, hsk⟩ := hweak
  letI := mΛ
  have hon (s : ℝ) (hs : s ∈ Icc 0 1) (f : ℝ → Fin k → ℝ) : onUnit f s = f s := by
    simp [onUnit, clamp01, max_eq_left hs.1, min_eq_left hs.2]
  have hUCae : ∀ᵐ ω ∂Q, rational_uc (y ω) := by
    rw [ae_iff]
    let E := {f : ℝ → Fin k → ℝ | rational_uc f}
    change Q (y ⁻¹' Eᶜ) = 0
    rw [← Measure.map_apply hy measurableSet_rational_uc.compl, hmapy,
      Measure.map_apply_of_aemeasurable hz measurableSet_rational_uc.compl]
    have hzero : (fun ω => onUnit (z ω)) ⁻¹' Eᶜ = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro ω h
      apply h
      exact cont_rational_uc ((hzcont ω).congr (fun s hs => hon s hs (z ω)))
    rw [hzero, measure_empty]
  have hGood : ∀ᵐ ω ∂Q, SkorohodTendsto (fun n => Y n ω) (y ω) ∧ rational_uc (y ω) :=
    hsk.and hUCae
  let E : Set Λ := {ω | ¬(SkorohodTendsto (fun n => Y n ω) (y ω) ∧ rational_uc (y ω))}
  obtain ⟨S, hsub, hSm, hSn⟩ := exists_measurable_superset_of_null (ae_iff.1 hGood)
  have hwell (ω : Λ) (hω : ω ∉ S) :
      SkorohodTendsto (fun n => Y n ω) (y ω) ∧ rational_uc (y ω) :=
    not_not.mp (fun h => hω (hsub h))
  have hSae : ∀ᵐ ω ∂Q, ω ∉ S := ae_iff.2 (by simpa using hSn)
  let Y₀ (n : ℕ) (ω : Λ) (t : ℝ) : Fin k → ℝ :=
    if ω ∈ S then 0 else w t • Y n ω (c t)
  let y₀ (ω : Λ) (t : ℝ) : Fin k → ℝ :=
    if ω ∈ S then 0 else w t • y ω (c t)
  let pull (f : ℝ → Fin k → ℝ) (t : ℝ≥0) := w t • f (c t)
  have hpull : Measurable pull := measurable_pi_lambda _ (fun t =>
    (measurable_pi_apply (c t)).const_smul (w t))
  refine ⟨Λ, mΛ, Q, Y₀, y₀, hQ, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hmapY] with n hn
    have h1 : AEMeasurable (pull ∘ Y n) Q := hpull.comp_aemeasurable (hY n).aemeasurable
    have h2 : AEMeasurable (pull ∘ fun ω => onUnit (Z n ω)) P := hpull.comp_aemeasurable (hZ n)
    have e1 : (pull ∘ Y n) =ᵐ[Q] (fun ω (t : NNReal) => Y₀ n ω t) :=
      hSae.mono (fun ω hω => by funext t; simp [Y₀, pull, hω])
    have e2 : (pull ∘ fun ω => onUnit (Z n ω)) = (fun ω (t : NNReal) => X n ω t) := by
      funext ω t
      exact (congrArg (fun v : Fin k → ℝ => w t • v)
        (hon _ ⟨(hc01 t t.2).1,(hc01 t t.2).2.le⟩ (Z n ω))).trans (hZeq n ω t t.2)
    refine ⟨h1.congr e1, e2 ▸ h2, ?_⟩
    rw [← Measure.map_congr e1, ← e2, ← map_map_meas_ae hpull
      (hY n).aemeasurable, hn, map_map_meas_ae hpull (hZ n)]
  · have h1 : AEMeasurable (pull ∘ y) Q := hpull.comp_aemeasurable hy.aemeasurable
    have h2 : AEMeasurable (pull ∘ fun ω => onUnit (z ω)) P' := hpull.comp_aemeasurable hz
    have e1 : (pull ∘ y) =ᵐ[Q] (fun ω (t : NNReal) => y₀ ω t) :=
      hSae.mono (fun ω hω => by funext t; simp [y₀, pull, hω])
    have e2 : (pull ∘ fun ω => onUnit (z ω)) = (fun ω (t : NNReal) => x ω t) := by
      funext ω t
      exact (congrArg (fun v : Fin k → ℝ => w t • v)
        (hon _ ⟨(hc01 t t.2).1,(hc01 t t.2).2.le⟩ (z ω))).trans (hzeq ω t t.2)
    refine ⟨h1.congr e1, e2 ▸ h2, ?_⟩
    rw [← Measure.map_congr e1, ← e2, ← map_map_meas_ae hpull
      hy.aemeasurable, hmapy, map_map_meas_ae hpull hz]
  · intro n ω i
    by_cases hω : ω ∈ S
    · simp only [Y₀, if_pos hω, Pi.zero_apply]
      exact ⟨fun _ _ => continuousWithinAt_const, fun _ _ => ⟨0,tendsto_const_nhds⟩⟩
    · simpa only [Y₀, if_neg hω, Pi.smul_apply, smul_eq_mul] using
        cadlag_of_pulled (Y n ω) ((hwell ω hω).1.1 n) c w hc hw hcm hc01 i
  · filter_upwards [hSae] with ω hω
    intro T hT
    have hup := sk_uniform (hwell ω hω).1 (rational_uc_to_uniform
      (hwell ω hω).1.2.1 (hwell ω hω).2)
    obtain ⟨A, hA⟩ := (isCompact_Icc (α := ℝ) (a := 0) (b := T)).exists_bound_of_continuousOn hw.continuousOn
    refine tendsto_order.2 ⟨fun a ha => (not_lt_zero ha).elim, fun b hb => ?_⟩
    obtain ⟨η, hη, hηb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hb
    let D : ℝ := (k:ℝ) * (|A| + 1) + 1
    have hD : 0 < D := by dsimp [D]; positivity
    have hηR : 0 < (η:ℝ) := by exact_mod_cast hη
    filter_upwards [hup ((η:ℝ)/(2*D)) (by positivity)] with n hn
    refine (show supDist (Y₀ n ω) (y₀ ω) T ≤ (η:ℝ≥0∞) from ?_).trans_lt hηb
    apply iSup₂_le
    intro s hs
    rw [ENNReal.coe_nnreal_eq]
    apply ENNReal.ofReal_le_ofReal
    have hws : |w s| ≤ |A|+1 := by
      have h := hA s hs
      rw [Real.norm_eq_abs] at h
      linarith [le_abs_self A]
    have hst : ‖Y n ω (c s) - y ω (c s)‖ < (η:ℝ)/(2*D) :=
      hn _ ⟨(hc01 s hs.1).1,(hc01 s hs.1).2.le⟩
    calc
      _ ≤ ∑ _ : Fin k, (|A|+1) * ((η:ℝ)/(2*D)) := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [Y₀, y₀, if_neg hω, Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul]
        refine mul_le_mul hws ?_ (abs_nonneg _) (by positivity)
        exact (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using
          norm_le_pi_norm (Y n ω (c s) - y ω (c s)) i :
          |Y n ω (c s) i - y ω (c s) i| ≤ ‖Y n ω (c s) - y ω (c s)‖).trans hst.le
      _ = ((k:ℝ) * (|A| + 1)) * ((η:ℝ)/(2*D)) := by simp [mul_assoc]
      _ ≤ (η:ℝ) := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity)).2
        dsimp [D]
        nlinarith [mul_nonneg (show 0 ≤ (k:ℝ) * (|A|+1) by positivity) hηR.le]


private theorem on_unit_eval {k : ℕ} (f : ℝ → Fin k → ℝ) {s : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) : onUnit f s = f s := by
  simp [onUnit,clamp01,max_eq_left hs.1,min_eq_left hs.2]

private theorem clamp_mem (s : ℝ) : clamp01 s ∈ Icc (0:ℝ) 1 := by
  change min (max s 0) 1 ∈ Icc (0:ℝ) 1
  exact ⟨le_min (le_max_right _ _) zero_le_one,min_le_right _ _⟩

private theorem on_unit_idempotent {k : ℕ} (f : ℝ → Fin k → ℝ) : onUnit (onUnit f) = onUnit f := by
  funext t
  exact on_unit_eval f (clamp_mem t)

private theorem cadlag_on_unit {k : ℕ} {f : ℝ → Fin k → ℝ} (h : IsCadlag01 f) : IsCadlag01 (onUnit f) := by
  constructor
  · intro s hs
    exact (h.1 s hs).congr (fun t ht => on_unit_eval f ⟨hs.1.trans ht.1,ht.2⟩)
      (on_unit_eval f ⟨hs.1,hs.2.le⟩)
  · intro s hs
    obtain ⟨l,hl⟩ := h.2 s hs
    refine ⟨l,hl.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (on_unit_eval f ⟨ht.1,ht.2.le.trans hs.2⟩).symm

private theorem right_on_unit {k : ℕ} {f : ℝ → Fin k → ℝ} (h : IsCadlag01 f) :
    ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt (onUnit f) (Ici s) s := by
  intro s hs
  by_cases h1 : s < 1
  · have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs,h1.le⟩
    have hClamp : clamp01 s = s := by simp [clamp01,max_eq_left hs,min_eq_left h1.le]
    have hCont : Continuous clamp01 := (continuous_id.max continuous_const).min continuous_const
    have hMap : MapsTo clamp01 (Ici s) (Icc s 1) := by
      intro t ht
      exact ⟨le_min (ht.trans (le_max_left _ _)) h1.le,(clamp_mem t).2⟩
    have hF : ContinuousWithinAt f (Icc s 1) (clamp01 s) := by rw [hClamp]; exact h.1 s ⟨hs,h1⟩
    exact hF.comp hCont.continuousWithinAt hMap
  · have he (t : ℝ) (ht : s ≤ t) : clamp01 t = 1 := by
      unfold clamp01
      exact min_eq_right ((le_of_not_gt h1).trans (ht.trans (le_max_left _ _)))
    exact continuousWithinAt_const.congr (fun t ht => show onUnit f t = f 1 from congrArg f (he t ht))
      (show onUnit f s = f 1 from congrArg f (he s le_rfl))

set_option maxHeartbeats 2600000 in
theorem solution {Ω : Type*} {Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ) (x : Ω' → ℝ → Fin k → ℝ)
    (hX : ∀ n ω i, IsCadlag (fun t => X n ω t i))
    (hXm : ∀ n t, 0 ≤ t → Measurable (fun ω => X n ω t))
    (hx : ∀ ω, ContinuousOn (x ω) (Ici 0))
    (hxm : ∀ t, 0 ≤ t → Measurable (fun ω => x ω t))
    (hF : ∀ (m : ℕ) (τ : Fin m → ℝ), (∀ i, 0 ≤ τ i) →
      TendstoInDistribution (fun n ω i => X n ω (τ i)) atTop
        (fun ω i => x ω (τ i)) (fun _ => P) P')
    (hM : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    CouplingConverges P P' X x := by
  classical
  let Z (n : ℕ) (ω : Ω) := onUnit (compactify (X n ω))
  let z (ω : Ω') := onUnit (compactify (x ω))
  have hZ (n : ℕ) : Measurable (Z n) := by
    apply measurable_pi_lambda
    intro t
    exact ((continuous_arctanVector.measurable.comp
      (hXm n _ (compressedTime_nonneg (clamp_mem t))))).const_smul (timeLeft (clamp01 t))
  have hz : Measurable z := by
    apply measurable_pi_lambda
    intro t
    exact ((continuous_arctanVector.measurable.comp
      (hxm _ (compressedTime_nonneg (clamp_mem t))))).const_smul (timeLeft (clamp01 t))
  have hzc (ω : Ω') : ContinuousOn (z ω) (Icc (0:ℝ) 1) :=
    ((compactified_path_regularity (x ω)).2 (hx ω)).congr (fun t ht => on_unit_eval _ ht)
  have hZc (n : ℕ) (ω : Ω) : IsCadlag01 (Z n ω) :=
    cadlag_on_unit ((compactified_path_regularity (X n ω)).1 (hX n ω))
  have hMc : ∀ (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1, |s-t| ≤ δ ∧
        ε ≤ ‖Z n ω s-Z n ω t‖} ≤ ENNReal.ofReal η := by
    intro ε η hε hη
    obtain ⟨δ,hδ,hD⟩ := compactified_path_modulus P X hM ε η hε hη
    refine ⟨δ,hδ,?_⟩
    filter_upwards [hD] with n hn
    refine (measure_mono ?_).trans hn
    rintro ω ⟨s,hs,t,ht,hd,hh⟩
    refine ⟨s,hs,t,ht,hd,?_⟩
    change ε ≤ ‖onUnit (compactify (X n ω)) s-onUnit (compactify (X n ω)) t‖ at hh
    rw [on_unit_eval _ hs,on_unit_eval _ ht] at hh
    exact hh
  have hFc : ∀ (m : ℕ) (τ : Fin m → ℝ), (∀ i, τ i ∈ Icc (0:ℝ) 1) →
      TendstoInDistribution (fun n ω i => Z n ω (τ i)) atTop
        (fun ω i => z ω (τ i)) (fun _ => P) P' := by
    intro m τ hτ
    let g (v : Fin m → Fin k → ℝ) (i : Fin m) := timeLeft (τ i) • arctanVector (v i)
    have hg : Continuous g := by
      apply continuous_pi
      intro i
      change Continuous (fun v : Fin m → Fin k → ℝ => timeLeft (τ i) • arctanVector (v i))
      have he : Continuous (fun v : Fin m → Fin k → ℝ => v i) := continuous_apply i
      exact (continuous_arctanVector.comp he).const_smul (timeLeft (τ i))
    have h := (hF m (fun i => compressedTime (τ i))
      (fun i => compressedTime_nonneg (hτ i))).continuous_comp hg
    simpa only [Z,z,on_unit_eval _ (hτ _),Function.comp_def,g,compactify] using h
  let C : Set (ℝ → Fin k → ℝ) := range (fun y : ℕ × Ω => Z y.1 y.2)
  let encode (n : ℕ) (ω : Ω) : C := ⟨Z n ω,⟨(n,ω),rfl⟩⟩
  let decode (w : C) : ℝ → Fin k → ℝ := w.1
  have hEnc (n : ℕ) : Measurable (encode n) := (hZ n).subtype_mk
  have hDec : Measurable decode := measurable_subtype_coe
  let Q (n : ℕ) := P.map (encode n)
  have hQ (n : ℕ) : IsProbabilityMeasure (Q n) := Measure.isProbabilityMeasure_map (hEnc n).aemeasurable
  have hRep (w : C) : ∃ n ω, decode w = Z n ω := by
    obtain ⟨⟨n,ω⟩,h⟩ := w.2
    exact ⟨n,ω,h.symm⟩
  have hDec0 (w : C) : onUnit (decode w) = decode w := by
    obtain ⟨n,ω,rfl'⟩ := hRep w
    rw [rfl']
    exact on_unit_idempotent _
  have heLaw (n : ℕ) : IdentDistrib (fun w : C => fun (t : ℝ≥0) => decode w t)
      (fun ω => fun (t : ℝ≥0) => Z n ω t) (Q n) P := by
    let ev (f : ℝ → Fin k → ℝ) (t : ℝ≥0) := f t
    have hev : Measurable ev := measurable_pi_lambda _ (fun t => measurable_pi_apply (t:ℝ))
    refine ⟨(hev.comp hDec).aemeasurable,(hev.comp (hZ n)).aemeasurable,?_⟩
    change (P.map (encode n)).map (ev ∘ decode) = P.map (ev ∘ Z n)
    rw [Measure.map_map (hev.comp hDec) (hEnc n)]
    rfl
  have hXcod : ∀ n, AEMeasurable (fun w : C => onUnit (decode w)) (Q n) ∧
      ∀ᵐ w ∂Q n, IsCadlag01 (decode w) := by
    intro n
    refine ⟨hDec.aemeasurable.congr (Eventually.of_forall fun w => (hDec0 w).symm),
      ae_of_all _ fun w => ?_⟩
    obtain ⟨j,ω,h⟩ := hRep w
    rw [h]
    exact hZc j ω
  have hFcod (m : ℕ) (τ : Fin m → ℝ) (hτ : ∀ j, τ j ∈ Icc (0:ℝ) 1)
      (f : (Fin m → Fin k → ℝ) → ℝ) (hBound : ∃ C, ∀ z, |f z| ≤ C)
      (hLip : ∃ L : ℝ≥0, LipschitzWith L f) :
      Tendsto (fun n => ∫ w : C, f (fun j => decode w (τ j)) ∂Q n) atTop
        (𝓝 (∫ ω, f (fun j => z ω (τ j)) ∂P')) := by
    obtain ⟨A,hA⟩ := hBound
    obtain ⟨L,hL⟩ := hLip
    let g := BoundedContinuousFunction.mkOfBound ⟨f,hL.continuous⟩ (2*A) (by
      intro u v
      rw [Real.dist_eq]
      change |f u-f v| ≤ 2*A
      exact (abs_sub _ _).trans (by linarith only [hA u,hA v]))
    have h := hFc m τ hτ
    have hg := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h.tendsto) g
    have hI (n : ℕ) :
        (∫ w : C, f (fun j => decode w (τ j)) ∂Q n) =
          ∫ ω, f (fun j => Z n ω (τ j)) ∂P := by
      apply integral_map (hEnc n).aemeasurable
      exact (hL.continuous.measurable.comp (measurable_pi_lambda _ (fun j =>
        (measurable_pi_apply (τ j)).comp hDec))).aestronglyMeasurable
    have hIn (n : ℕ) : (∫ u, g u ∂(P.map (fun ω j => Z n ω (τ j)))) =
        ∫ ω, f (fun j => Z n ω (τ j)) ∂P :=
      integral_map (h.forall_aemeasurable n) g.continuous.measurable.aestronglyMeasurable
    have hOut : (∫ u, g u ∂(P'.map (fun ω j => z ω (τ j)))) =
        ∫ ω, f (fun j => z ω (τ j)) ∂P' :=
      integral_map h.aemeasurable_limit g.continuous.measurable.aestronglyMeasurable
    change Tendsto (fun n => ∫ u, g u ∂(P.map (fun ω j => Z n ω (τ j)))) atTop
      (𝓝 (∫ u, g u ∂(P'.map (fun ω j => z ω (τ j))))) at hg
    simpa only [hI,hIn,hOut] using hg
  have hMcod : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      Q n {ω : C | ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1, |s-t| ≤ δ ∧
        ε ≤ ‖decode ω s-decode ω t‖} ≤ ENNReal.ofReal η := by
    intro ε hε η hη
    obtain ⟨δ,hδ,hN⟩ := hMc (ε/2) η (by positivity) hη
    obtain ⟨N,hN⟩ := eventually_atTop.1 hN
    refine ⟨δ/2,by positivity,N,fun n hn => ?_⟩
    have hright (w : C) : ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt (decode w) (Ici s) s := by
      obtain ⟨j,ω,he⟩ := hRep w
      rw [he]
      exact right_on_unit ((compactified_path_regularity (X j ω)).1 (hX j ω))
    have h := path_law_modulus_transfer decode (Z n) (heLaw n) hright 1 (δ/2) ε
      (by positivity) hε
    simp only [Nat.cast_one,dist_eq_norm,show 2*(δ/2) = δ by ring] at h
    exact h.trans (hN n hn)
  have hW := weakConvD_of_fdd_and_modulus Q (fun _ (w : C) => decode w) P' z
    hQ inferInstance hXcod (fun t => (measurable_pi_apply t).comp hz) hzc hFcod hMcod
  have hLift : ∃ (Λ : Type) (_ : MeasurableSpace Λ) (R : Measure Λ)
      (U : ℕ → Λ → ℝ → Fin k → ℝ) (v : Λ → ℝ → Fin k → ℝ),
      IsProbabilityMeasure R ∧ (∀ n, Measurable (U n)) ∧ Measurable v ∧
      (∀ᶠ n in atTop, R.map (U n) = P.map (fun ω => onUnit (Z n ω))) ∧
      R.map v = P'.map (fun ω => onUnit (z ω)) ∧
      ∀ᵐ ω ∂ R, SkorohodTendsto (fun n => U n ω) (v ω) := by
    obtain ⟨Λ,mΛ,R,U,v,hR,hU,hv,hUL,hvL,hConv⟩ := hW
    letI := mΛ
    refine ⟨Λ,mΛ,R,U,v,hR,hU,hv,?_,hvL,hConv⟩
    filter_upwards [hUL] with n hn
    have hDecode : (fun w => onUnit (decode w)) = decode := funext hDec0
    rw [hn,hDecode]
    change (P.map (encode n)).map decode = _
    rw [Measure.map_map hDec (hEnc n)]
    have hzEq : (fun ω => onUnit (Z n ω)) = Z n := funext (fun ω => on_unit_idempotent _)
    rw [hzEq]
    rfl
  have hI : ∀ ω i, IsCadlag (fun t => x ω t i) := by
    intro ω i
    have h := (continuous_apply i).comp_continuousOn (hx ω)
    constructor
    · intro t ht
      exact (h t ht).mono (Ici_subset_Ici.2 ht)
    · intro t ht
      refine ⟨x ω t i, (h t ht.le).mono_left ?_⟩
      apply le_inf nhdsWithin_le_nhds
      rw [le_principal_iff]
      exact mem_nhdsWithin_of_mem_nhds (mem_of_superset (Ioi_mem_nhds ht) Ioi_subset_Ici_self)
  refine arctan_coupling_recovery P P' X x hX hI ?_
  apply coupled_unit_law_lift P P' (fun n ω t => arctanVector (X n ω t))
    (fun ω t => arctanVector (x ω t)) Z z unitEmbed unweight continuous_unitEmbed
    (continuous_const.add (continuous_id.max continuous_const)) unitEmbed_mono
    (fun _ ht => unitEmbed_bounds ht)
  · intro n ω t ht
    simp only [Z,on_unit_eval _ ⟨(unitEmbed_bounds ht).1,(unitEmbed_bounds ht).2.le⟩]
    exact compactify_inverse _ ht
  · intro ω t ht
    simp only [z,on_unit_eval _ ⟨(unitEmbed_bounds ht).1,(unitEmbed_bounds ht).2.le⟩]
    exact compactify_inverse _ ht
  · intro n
    exact (hZ n).aemeasurable.congr (Eventually.of_forall fun ω => (on_unit_idempotent _).symm)
  · exact hz.aemeasurable.congr (Eventually.of_forall fun ω => (on_unit_idempotent _).symm)
  · exact hzc
  · exact hLift
