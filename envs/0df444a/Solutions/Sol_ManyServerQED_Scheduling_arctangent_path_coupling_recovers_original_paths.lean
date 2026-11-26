-- Prove2me | solution 1 for ManyServerQED.Scheduling.arctangent_path_coupling_recovers_original_paths
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:06:37.860365+00:00
-- url     : https://prove2.me/submissions/5b5cd6b3-7613-4059-9cb1-4426508d1b35

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open BellWilliams2001.ThresholdPolicy

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
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
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
