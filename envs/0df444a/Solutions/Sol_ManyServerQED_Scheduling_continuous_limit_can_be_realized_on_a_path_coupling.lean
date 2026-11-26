-- Prove2me | solution 1 for ManyServerQED.Scheduling.continuous_limit_can_be_realized_on_a_path_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:39:33.706393+00:00
-- url     : https://prove2.me/submissions/a93caaa9-75f3-4b63-817a-bc76a39687f7

import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Reiman84.QueueLength BellWilliams2001.ThresholdPolicy

private theorem rational_near_cadlag {k : ℕ} {f : ℝ → Fin k → ℝ} (hf : ∀ t ∈ Ico (0:ℝ) 1, ContinuousWithinAt f (Icc t 1) t)
    {t ε : ℝ} (ht : t ∈ Icc 0 1) (hε : 0 < ε) :
    ∃ q : ℚ, (q:ℝ) ∈ Icc 0 1 ∧ dist (q:ℝ) t < ε ∧ dist (f q) (f t) < ε := by
  rcases ht.2.lt_or_eq with h | h
  · obtain ⟨δ, hδ, hV⟩ := Metric.continuousWithinAt_iff.mp (hf t ⟨ht.1,h⟩) ε hε
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
    (hf : ∀ t ∈ Ico (0:ℝ) 1, ContinuousWithinAt f (Icc t 1) t) (hu : rational_uc f) : UniformContinuousOn f (Icc 0 1) := by
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


private theorem continuous_from_rational_windows {k : ℕ} (v : ℝ → Fin k → ℝ)
    (hRight : ∀ i t, 0 ≤ t → ContinuousWithinAt (fun s => v s i) (Ici t) t)
    (hR : ∀ N : ℕ, rational_uc (fun s => v ((N+1:ℕ)*s))) :
    ContinuousOn v (Ici (0:ℝ)) := by
  intro t ht
  obtain ⟨N,hN⟩ := exists_nat_gt t
  let c : ℝ := (N+1:ℕ)
  have hc : 0 < c := by dsimp [c]; positivity
  have htc : t < c := by dsimp [c]; exact hN.trans_le (by push_cast; linarith)
  have hRc (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      ContinuousWithinAt (fun u => v (c*u)) (Icc s 1) s := by
    apply continuousWithinAt_pi.2
    intro i
    have hm : MapsTo (fun u : ℝ => c*u) (Icc s 1) (Ici (c*s)) := by
      intro u hu
      exact mul_le_mul_of_nonneg_left hu.1 hc.le
    exact (hRight i (c*s) (mul_nonneg hc.le hs.1)).comp
      ((continuous_const.mul continuous_id).continuousWithinAt) hm
  have hU := rational_uc_to_uniform hRc (hR N)
  have hTin : t/c ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg ht hc.le,(div_le_one hc).2 htc.le⟩
  have hV : ContinuousWithinAt (fun s => v (c*s)) (Icc (0:ℝ) 1) (t/c) := hU.continuousOn _ hTin
  have hInv : MapsTo (fun s : ℝ => s/c) (Icc (0:ℝ) c) (Icc (0:ℝ) 1) := by
    intro s hs
    exact ⟨div_nonneg hs.1 hc.le,(div_le_one hc).2 hs.2⟩
  have hlocal : ContinuousWithinAt v (Icc (0:ℝ) c) t := by
    have hc0 : ContinuousWithinAt (fun s : ℝ => s/c) (Icc (0:ℝ) c) t :=
      (continuous_id.div_const c).continuousWithinAt
    have hh : ContinuousWithinAt ((fun s => v (c*s)) ∘ (fun s : ℝ => s/c)) (Icc (0:ℝ) c) t :=
      hV.tendsto.comp (hc0.tendsto_nhdsWithin hInv)
    have he : ((fun s => v (c*s)) ∘ (fun s : ℝ => s/c)) = v := by
      funext s
      change v (c*(s/c)) = v s
      congr 1
      field_simp
    rwa [he] at hh
  apply hlocal.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htc)]
    with s hs hsc
  exact ⟨hs,hsc.le⟩

set_option maxHeartbeats 1800000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (P : Measure Ω) (P' : Measure Ω')
    (X : ℕ → Ω → ℝ → Fin k → ℝ) (x : Ω' → ℝ → Fin k → ℝ)
    (hx : ∀ ω, ContinuousOn (x ω) (Ici (0:ℝ)))
    (h : CouplingConverges P P' X x) :
    ∃ (Λ : Type) (_ : MeasurableSpace Λ) (Q : Measure Λ)
      (Y : ℕ → Λ → ℝ → Fin k → ℝ) (v : Λ → ℝ → Fin k → ℝ),
      IsProbabilityMeasure Q ∧
      (∀ᶠ n in atTop, IdentDistrib (fun ω (t : ℝ≥0) => Y n ω t)
        (fun ω (t : ℝ≥0) => X n ω t) Q P) ∧
      IdentDistrib (fun ω (t : ℝ≥0) => v ω t) (fun ω (t : ℝ≥0) => x ω t) Q P' ∧
      (∀ n ω i, IsCadlag (fun t => Y n ω t i)) ∧
      (∀ ω, ContinuousOn (v ω) (Ici (0:ℝ))) ∧
      (∀ t : ℝ≥0, Measurable (fun ω => v ω t)) ∧
      ∀ᵐ ω ∂Q, ∀ T : ℝ, 0 ≤ T → Tendsto (fun n => supDist (Y n ω) (v ω) T) atTop (𝓝 0) := by
  classical
  obtain ⟨Λ,mΛ,Q,Y,w,hQ,hLaw,hwLaw,hCad,hConv⟩ := h
  letI := mΛ
  have hR (N : ℕ) : ∀ᵐ ω ∂Q, rational_uc (fun s => w ω ((N+1:ℕ)*s)) := by
    let eval (f : ℝ≥0 → Fin k → ℝ) (s : ℝ) := f ((((N+1:ℕ):ℝ)*s).toNNReal)
    have hm : Measurable eval :=
      measurable_pi_lambda _ (fun s => measurable_pi_apply ((((N+1:ℕ):ℝ)*s).toNNReal))
    have hh := hwLaw.comp hm
    have hL (ω : Ω') : rational_uc (eval (fun t : ℝ≥0 => x ω t)) := by
      apply cont_rational_uc
      have hM : MapsTo (fun s : ℝ => ((N+1:ℕ):ℝ)*s) (Icc (0:ℝ) 1) (Ici (0:ℝ)) :=
        fun s hs => mul_nonneg (Nat.cast_nonneg _) hs.1
      have hco := (hx ω).comp ((continuous_const.mul continuous_id).continuousOn) hM
      apply hco.congr
      intro s hs
      change x ω ((((N+1:ℕ):ℝ)*s).toNNReal:ℝ) = x ω (((N+1:ℕ):ℝ)*s)
      rw [Real.coe_toNNReal _ (hM hs)]
    let E : Set (ℝ → Fin k → ℝ) := {p | rational_uc p}
    have hE : MeasurableSet Eᶜ := measurableSet_rational_uc.compl
    have hEq := congrArg (fun μ : Measure (ℝ → Fin k → ℝ) => μ Eᶜ) hh.map_eq
    rw [Measure.map_apply_of_aemeasurable hh.aemeasurable_fst hE,
      Measure.map_apply_of_aemeasurable hh.aemeasurable_snd hE] at hEq
    have h0 : (eval ∘ fun ω (t : ℝ≥0) => x ω t) ⁻¹' Eᶜ = ∅ := by
      ext ω
      exact ⟨fun h => (h (hL ω)).elim,False.elim⟩
    rw [h0,measure_empty] at hEq
    have hAE : ∀ᵐ ω ∂Q, rational_uc (eval (fun t : ℝ≥0 => w ω t)) := ae_iff.2 hEq
    filter_upwards [hAE] with ω hω
    intro m
    obtain ⟨j,hj⟩ := hω m
    exact ⟨j,fun u v hu hv huv => by
      have hu0 : 0 ≤ ((N+1:ℕ):ℝ)*(u:ℝ) := mul_nonneg (Nat.cast_nonneg _) hu.1
      have hv0 : 0 ≤ ((N+1:ℕ):ℝ)*(v:ℝ) := mul_nonneg (Nat.cast_nonneg _) hv.1
      simpa only [eval,Real.coe_toNNReal _ hu0,Real.coe_toNNReal _ hv0] using hj u v hu hv huv⟩
  have hCW : ∀ᵐ ω ∂Q, ContinuousOn (w ω) (Ici (0:ℝ)) := by
    filter_upwards [hConv,ae_all_iff.2 hR] with ω hω hR
    exact continuous_from_rational_windows (w ω)
      (right_limit_of_uoc (fun n i => hCad n ω i) hω) hR
  obtain ⟨Bad,hBad,hmBad,h0⟩ := exists_measurable_superset_of_null (ae_iff.1 hCW)
  let v (ω : Λ) (t : ℝ) : Fin k → ℝ := if ω ∈ Bad then 0 else w ω t
  have hEg : ∀ᵐ ω ∂Q, ω ∉ Bad := ae_iff.2 (by simpa using h0)
  have hEq : (fun ω (t : ℝ≥0) => w ω t) =ᵐ[Q] fun ω (t : ℝ≥0) => v ω t := by
    filter_upwards [hEg] with ω hω
    funext t
    simp [v,hω]
  have hIdent := (IdentDistrib.of_ae_eq hwLaw.aemeasurable_fst hEq).symm.trans hwLaw
  let vM := hIdent.aemeasurable_fst.mk (fun ω (t : ℝ≥0) => v ω t)
  have hvM : Measurable vM := hIdent.aemeasurable_fst.measurable_mk
  have hEqM : ∀ᵐ ω ∂Q, (fun t : ℝ≥0 => v ω t) = vM ω := hIdent.aemeasurable_fst.ae_eq_mk
  obtain ⟨Bad',hBad',hmBad',h0'⟩ := exists_measurable_superset_of_null (ae_iff.1 hEqM)
  have hEg' : ∀ᵐ ω ∂Q, ω ∉ Bad' := ae_iff.2 (by simpa using h0')
  let v' (ω : Λ) (t : ℝ) : Fin k → ℝ := if ω ∈ Bad' then 0 else v ω t
  have hEq' : (fun ω (t : ℝ≥0) => v ω t) =ᵐ[Q] fun ω (t : ℝ≥0) => v' ω t := by
    filter_upwards [hEg'] with ω hω
    funext t
    simp [v',hω]
  have hVm (t : ℝ≥0) : Measurable (fun ω => v' ω t) := by
    have h : (fun ω => v' ω t) = fun ω => if ω ∈ Bad' then 0 else vM ω t := by
      funext ω
      by_cases hω : ω ∈ Bad'
      · simp [v',hω]
      · have he := not_not.mp (fun hc => hω (hBad' hc))
        simp only [v',if_neg hω,congrFun he t]
    rw [h]
    exact Measurable.ite hmBad' measurable_const ((measurable_pi_apply t).comp hvM)
  refine ⟨Λ,mΛ,Q,Y,v',hQ,hLaw,(IdentDistrib.of_ae_eq hIdent.aemeasurable_fst hEq').symm.trans hIdent,
    hCad,?_,hVm,?_⟩
  · intro ω
    by_cases hω : ω ∈ Bad' <;> by_cases hw : ω ∈ Bad
    · simpa only [v',if_pos hω] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : Fin k → ℝ)) (Ici 0))
    · simpa only [v',if_pos hω] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : Fin k → ℝ)) (Ici 0))
    · simpa only [v',v,if_neg hω,if_pos hw] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : Fin k → ℝ)) (Ici 0))
    · simpa only [v',v,if_neg hω,if_neg hw] using not_not.mp (fun hc => hw (hBad hc))
  · filter_upwards [hConv,hEg,hEg'] with ω hω ha hb
    simpa only [v',v,if_neg ha,if_neg hb] using hω
