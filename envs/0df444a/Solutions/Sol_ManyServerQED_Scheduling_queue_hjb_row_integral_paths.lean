-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_row_integral_paths
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:27:37.583028+00:00
-- url     : https://prove2.me/submissions/6c39a030-9854-4a7f-994b-807fcad3ef8b

import Theorems.Thm_ManyServerQED_Scheduling_controlled_queue_state_and_effective_noise_are_cadlag
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_integrands_on_bounded_state_sets
import Theorems.Thm_ManyServerQED_Scheduling_queue_state_and_allocation_jointly_measurable_in_past
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

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

set_option maxHeartbeats 2200000 in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (γ ϱ mL : ℝ) (hA2 : Assumption2 Lt ϱ mL)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (f : (Fin k → ℝ) → ℝ) (hH : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (X0 : ℕ → Fin k → ℕ)
    (hC : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n)) :
    let z (n : ℕ) (ω : Ω) := M.Xhat n (X n) ω
    let u (n : ℕ) (ω : Ω) := uProc n u0 (X n) (Ψ n) ω
    let b (n : ℕ) (ω : Ω) (t : ℝ) := drift M.diffData (z n ω t) (u n ω t)
    let c (n : ℕ) (ω : Ω) (t : ℝ) := Real.exp (-γ*t) * costOfTilde Lt (z n ω t) (u n ω t)
    let g (n : ℕ) (ω : Ω) (t : ℝ) :=
      Real.exp (-γ*t)*((∑ i, b n ω t i*grad f (z n ω t) i)+costOfTilde Lt (z n ω t) (u n ω t)-
        hamiltonian M.diffData (costOfTilde Lt) (z n ω t) (grad f (z n ω t)))
    let B (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) := ∫ s in (0:ℝ)..t, b n ω s i
    let C (n : ℕ) (ω : Ω) (t : ℝ) := ∫ s in (0:ℝ)..t, c n ω s
    let G (n : ℕ) (ω : Ω) (t : ℝ) := ∫ s in (0:ℝ)..t, g n ω s
    (∀ n, 1 ≤ n → ∀ ω,
      (∀ i, ContinuousOn (fun t => B n ω t i) (Ici 0)) ∧
      ContinuousOn (C n ω) (Ici 0) ∧ ContinuousOn (G n ω) (Ici 0) ∧
      MonotoneOn (C n ω) (Ici 0) ∧ MonotoneOn (G n ω) (Ici 0) ∧
      (∀ T : ℝ, 0 ≤ T → ENNReal.ofReal (C n ω T) =
        ∫⁻ t in Ioc (0:ℝ) T, ENNReal.ofReal (c n ω t) ∂volume) ∧
      (∀ T : ℝ, 0 ≤ T →
        (∀ i, IntervalIntegrable (fun t => b n ω t i) volume 0 T) ∧
        IntervalIntegrable (c n ω) volume 0 T ∧ IntervalIntegrable (g n ω) volume 0 T) ∧
      (∀ t : ℝ, 0 ≤ t → u n ω t ∈ stdSimplex ℝ (Fin k))) ∧
    (∀ T A : ℝ, ∃ a > 0, ∀ n, 1 ≤ n → ∀ ω,
      (∀ t ∈ Icc (0:ℝ) T, ‖z n ω t‖ ≤ A) →
      ∀ s ∈ Icc (0:ℝ) T, ∀ t ∈ Icc (0:ℝ) T,
        (∀ i, |B n ω s i-B n ω t i| ≤ a*|s-t|) ∧
        |C n ω s-C n ω t| ≤ a*|s-t| ∧ |G n ω s-G n ω t| ≤ a*|s-t|) := by
  intro z u b c g B C G
  classical
  obtain ⟨hLc,hc,hg,hNonneg,_,hLoc⟩ :=
    queue_hjb_integrands_on_bounded_state_sets M.diffData Lt γ ϱ mL hA2 f hH
  have hU (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
      u n ω t ∈ stdSimplex ℝ (Fin k) := by
    change uProc n u0 (X n) (Ψ n) ω t ∈ stdSimplex ℝ (Fin k)
    unfold uProc
    split_ifs with hh
    · refine ⟨fun i => div_nonneg ((hC n hn).controlled.phi_nonneg ω t i ht) hh.le,?_⟩
      rw [← Finset.sum_div, ← hWork n hn ω t ht, max_eq_left hh.le, div_self hh.ne']
    · exact hu0
  have hMeas (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (T : ℝ) (hT : 0 ≤ T) :
      (∀ i, AEStronglyMeasurable (fun t => b n ω t i) (volume.restrict (Icc 0 T))) ∧
      AEStronglyMeasurable (c n ω) (volume.restrict (Icc 0 T)) ∧
      AEStronglyMeasurable (g n ω) (volume.restrict (Icc 0 T)) := by
    let Tv : ℝ≥0 := ⟨T,hT⟩
    let uT (t : ℝ) := min (t.toNNReal:ℝ) T
    have hCl (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) : uT t = t := by
      dsimp [uT]
      rw [max_eq_left ht.1,min_eq_left ht.2]
    have hS := queue_state_and_allocation_jointly_measurable_in_past M n (X0 n)
      (X n) (Ψ n) (hC n hn) Tv
    let j (t : ℝ) : Ω × ℝ≥0 := (ω,t.toNNReal)
    have hj : @Measurable ℝ (Ω × ℝ≥0) _ (@MeasurableSpace.prod Ω ℝ≥0
        (M.pastInfo n (X n) (Ψ n) T) _) j :=
      measurable_const.prodMk measurable_id.real_toNNReal
    have hX : Measurable (fun t => X n ω (uT t)) := hS.1.comp hj
    have hP : Measurable (fun t => Ψ n ω (uT t)) := hS.2.comp hj
    have hz : Measurable (fun t => z n ω (uT t)) := by
      apply measurable_pi_lambda
      intro i
      exact (((measurable_pi_apply i).comp hX).sub_const (M.rho i*n)).div_const _
    have hu : Measurable (fun t => u n ω (uT t)) := by
      let a (t : ℝ) := (∑ i, X n ω (uT t) i) - (n:ℝ)
      have ha : Measurable a :=
        (Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).comp hX)).sub_const _
      apply measurable_pi_lambda
      intro i
      simp only [u,uProc,ite_apply]
      exact Measurable.ite (measurableSet_lt measurable_const ha)
        ((((measurable_pi_apply i).comp hX).sub ((measurable_pi_apply i).comp hP)).div ha) measurable_const
    have hb : Continuous (fun p : (Fin k → ℝ) × (Fin k → ℝ) => drift M.diffData p.1 p.2) := by
      unfold drift
      fun_prop
    have hTme : Measurable uT := measurable_id.real_toNNReal.coe_nnreal_real.min measurable_const
    have hPair := hz.prodMk hu
    have hTriple := hTme.prodMk hPair
    have transfer (v : ℝ → ℝ) (hm : Measurable (fun t => v (uT t))) :
        AEStronglyMeasurable v (volume.restrict (Icc 0 T)) :=
      hm.aestronglyMeasurable.congr ((ae_restrict_mem measurableSet_Icc).mono
        fun t ht => by change v (uT t) = v t; rw [hCl t ht])
    exact ⟨fun i => transfer _ ((continuous_apply i).measurable.comp (hb.measurable.comp hPair)),
      transfer _ (hc.measurable.comp hTriple),transfer _ (hg.measurable.comp hTriple)⟩
  have hIt (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (T : ℝ) (hT : 0 ≤ T) :
      (∀ i, IntervalIntegrable (fun t => b n ω t i) volume 0 T) ∧
      IntervalIntegrable (c n ω) volume 0 T ∧ IntervalIntegrable (g n ω) volume 0 T := by
    have hBd (i : Fin k) := cadlag_compact_bounds (fun t => z n ω t i)
      (controlled_queue_state_and_effective_noise_are_cadlag M n hn (X0 n) (X n) (Ψ n)
        (hC n hn).controlled ω i).1 T
    choose V hV hV' using hBd
    let A := ∑ i, V i
    have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hV i)
    have hBound (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) : ‖z n ω t‖ ≤ A :=
      (pi_norm_le_iff_of_nonneg hA).2 (fun i => by
        rw [Real.norm_eq_abs]
        exact (hV' i t ht).trans (Finset.single_le_sum (fun j _ => hV j) (Finset.mem_univ i)))
    obtain ⟨a,ha,hL⟩ := hLoc T A
    have hMs := hMeas n hn ω T hT
    have getInt (v : ℝ → ℝ) (hm : AEStronglyMeasurable v (volume.restrict (Icc 0 T)))
        (hBound : ∀ t ∈ Icc (0:ℝ) T, |v t| ≤ a) : IntervalIntegrable v volume 0 T := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le hT enorm_ne_top).2
      letI : IsFiniteMeasure (volume.restrict (Icc 0 T)) :=
        isFiniteMeasure_restrict.2 (Real.volume_Icc .. ▸ ENNReal.ofReal_ne_top)
      refine ⟨hm,HasFiniteIntegral.of_bounded (C := a) ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simpa only [Real.norm_eq_abs] using hBound t ht
    exact ⟨fun i => getInt _ (hMs.1 i)
      (fun t ht => (hL t ht _ _ (hBound t ht) (hU n hn ω t ht.1)).1 i),
      getInt _ hMs.2.1 (fun t ht => (hL t ht _ _ (hBound t ht) (hU n hn ω t ht.1)).2.1),
      getInt _ hMs.2.2 (fun t ht => (hL t ht _ _ (hBound t ht) (hU n hn ω t ht.1)).2.2)⟩
  have hCont (v : ℝ → ℝ) (hv : ∀ t, 0 ≤ t → IntervalIntegrable v volume 0 t) :
      ContinuousOn (fun t => ∫ s in (0:ℝ)..t, v s) (Ici 0) := by
    intro t ht
    have hpos : (0:ℝ) ≤ t+1 := by linarith [show 0 ≤ t from ht]
    have he : ContinuousOn (fun t => ∫ s in (0:ℝ)..t, v s) (Icc (0:ℝ) (t+1)) := by
      simpa only [uIcc_of_le hpos] using intervalIntegral.continuousOn_primitive_interval'
        (hv (t+1) hpos) (left_mem_uIcc (a := (0:ℝ)) (b := t+1))
    have hN : Icc (0:ℝ) (t+1) ∈ 𝓝[Ici 0] t := by
      rw [← Ici_inter_Iic, inter_mem_iff]
      exact ⟨self_mem_nhdsWithin,nhdsWithin_le_nhds (Iic_mem_nhds (show t < t+1 by linarith))⟩
    exact (he t ⟨ht,by linarith⟩).mono_of_mem_nhdsWithin hN
  have hMono (v : ℝ → ℝ) (hv : ∀ t, 0 ≤ t → IntervalIntegrable v volume 0 t)
      (hp : ∀ t, 0 ≤ t → 0 ≤ v t) :
      MonotoneOn (fun t => ∫ s in (0:ℝ)..t, v s) (Ici 0) := by
    intro s hs t ht hst
    have hm := intervalIntegral.integral_add_adjacent_intervals (hv s hs) ((hv s hs).symm.trans (hv t ht))
    have hn := intervalIntegral.integral_nonneg (μ := volume) hst (fun r hr => hp r (hs.trans hr.1))
    linarith
  refine ⟨?_,?_⟩
  · intro n hn ω
    have hN (t : ℝ) (ht : (0:ℝ) ≤ t) := hNonneg t (z n ω t) (u n ω t) (hU n hn ω t ht)
    exact ⟨fun i => hCont _ (fun t ht => (hIt n hn ω t ht).1 i),
      hCont _ (fun t ht => (hIt n hn ω t ht).2.1), hCont _ (fun t ht => (hIt n hn ω t ht).2.2),
      hMono _ (fun t ht => (hIt n hn ω t ht).2.1) (fun t ht => (hN t ht).1),
      hMono _ (fun t ht => (hIt n hn ω t ht).2.2) (fun t ht => (hN t ht).2),
      fun t ht => by
        dsimp [C]
        rw [intervalIntegral.integral_of_le ht]
        exact ofReal_integral_eq_lintegral_ofReal ((hIt n hn ω t ht).2.1.1)
          ((ae_restrict_mem measurableSet_Ioc).mono fun r hr => (hN r hr.1.le).1),
      hIt n hn ω,hU n hn ω⟩
  · intro T A
    obtain ⟨a,ha,hBound⟩ := hLoc T A
    refine ⟨a,ha,?_⟩
    intro n hn ω hB s hs t ht
    have hB' (r : ℝ) (hr : r ∈ Icc (0:ℝ) T) :=
      hBound r hr (z n ω r) (u n ω r) (hB r hr) (hU n hn ω r hr.1)
    have hLip (v : ℝ → ℝ) (hVs : IntervalIntegrable v volume 0 s)
        (hVt : IntervalIntegrable v volume 0 t) (hV : ∀ r ∈ Icc (0:ℝ) T, |v r| ≤ a) :
        |(∫ r in (0:ℝ)..s, v r)-(∫ r in (0:ℝ)..t, v r)| ≤ a*|s-t| := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hVt (hVt.symm.trans hVs),add_sub_cancel_left]
      have hAbs := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := t) (b := s) (C := a) (fun r hr => by
          rw [Real.norm_eq_abs]
          change r ∈ Ioc (min t s) (max t s) at hr
          exact hV r ⟨(le_min ht.1 hs.1).trans hr.1.le,hr.2.trans (max_le ht.2 hs.2)⟩)
      simpa only [Real.norm_eq_abs] using hAbs
    exact ⟨fun i => hLip _ ((hIt n hn ω s hs.1).1 i) ((hIt n hn ω t ht.1).1 i)
      (fun r hr => (hB' r hr).1 i),
      hLip _ (hIt n hn ω s hs.1).2.1 (hIt n hn ω t ht.1).2.1 (fun r hr => (hB' r hr).2.1),
      hLip _ (hIt n hn ω s hs.1).2.2 (hIt n hn ω t ht.1).2.2 (fun r hr => (hB' r hr).2.2)⟩
