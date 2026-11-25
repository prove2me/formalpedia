-- Prove2me | solution 1 for ManyServerQED.Scheduling.unit_interval_coupling_lift
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:39:12.671863+00:00
-- url     : https://prove2.me/submissions/b580a324-ff83-4610-ba4e-c7c3d205b347

import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Reiman84.QueueLength BellWilliams2001.ThresholdPolicy

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
theorem solution {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {k : ℕ}
    (P : Measure Ω) (P' : Measure Ω') (X : ℕ → Ω → ℝ → Fin k → ℝ)
    (x : Ω' → ℝ → Fin k → ℝ) (Z : ℕ → Ω → ℝ → Fin k → ℝ) (z : Ω' → ℝ → Fin k → ℝ)
    (c w : ℝ → ℝ) (hc : Continuous c) (hw : Continuous w)
    (hcm : StrictMonoOn c (Ici 0)) (hc01 : ∀ t : ℝ, 0 ≤ t → c t ∈ Ico 0 1)
    (hZeq : ∀ n ω t, 0 ≤ t → w t • Z n ω (c t) = X n ω t)
    (hzeq : ∀ ω t, 0 ≤ t → w t • z ω (c t) = x ω t)
    (hZ : ∀ n, AEMeasurable (fun ω => onUnit (Z n ω)) P)
    (hz : AEMeasurable (fun ω => onUnit (z ω)) P')
    (hzcont : ∀ ω, ContinuousOn (z ω) (Icc 0 1))
    (hweak : WeakConvD (fun _ => P) Z P' z) :
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
