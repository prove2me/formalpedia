-- Prove2me | solution 1 for ManyServerQED.Scheduling.scp_joint_state_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:57:45.3457+00:00
-- url     : https://prove2.me/submissions/3499c683-0d9d-4d90-a265-eb02f6f3a0dc

import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Definitions.Def_ManyServerQED_Scheduling_Policy
import Mathlib

open Set MeasureTheory Filter Topology

private theorem measurable_unique_graph_section {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] [StandardBorelSpace E] [StandardBorelSpace F]
    (G : Set (E × F)) (hG : MeasurableSet G)
    (hu : ∀ {a : E} {b c : F}, (a,b) ∈ G → (a,c) ∈ G → b = c)
    (u : Ω → E) (huM : Measurable u) (v : Ω → F)
    (hv : ∀ ω, (u ω, v ω) ∈ G) : Measurable v := by
  let f : G → E := fun p => p.val.1
  letI : StandardBorelSpace G := hG.standardBorel
  have hf : Measurable f := measurable_fst.comp measurable_subtype_coe
  have hi : Function.Injective f := by
    rintro ⟨⟨a,b⟩,hp⟩ ⟨⟨c,d⟩,hq⟩ h
    change a = c at h
    subst c
    exact Subtype.ext (Prod.ext rfl (hu hp hq))
  let z (ω : Ω) : G := ⟨(u ω,v ω), hv ω⟩
  have hz : Measurable z := (hf.measurableEmbedding hi).measurable_comp_iff.1 huM
  exact (measurable_snd.comp measurable_subtype_coe).comp hz

private theorem scalar_monotone_clock_eq {T : ℝ} (hT : 0 ≤ T)
    (R u v : ℝ → ℝ) (hR : Monotone R)
    (huc : ContinuousOn u (Icc 0 T)) (hvc : ContinuousOn v (Icc 0 T))
    (hu : IntervalIntegrable (fun s => R (u s)) volume 0 T)
    (hv : IntervalIntegrable (fun s => R (v s)) volume 0 T)
    (heq : ∀ t ∈ Icc 0 T, u t - v t = ∫ s in (0:ℝ)..t, (R (v s) - R (u s))) :
    EqOn u v (Icc 0 T) := by
  have less {u v : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 T)) (hvc : ContinuousOn v (Icc 0 T))
      (hu : IntervalIntegrable (fun s => R (u s)) volume 0 T)
      (hv : IntervalIntegrable (fun s => R (v s)) volume 0 T)
      (heq : ∀ t ∈ Icc 0 T, u t - v t = ∫ s in (0:ℝ)..t, (R (v s) - R (u s))) :
      ∀ t ∈ Icc 0 T, u t ≤ v t := by
    intro t ht
    by_contra! h
    let d (s : ℝ) := u s - v s
    have hdt : 0 < d t := sub_pos.mpr h
    have hdc : ContinuousOn d (Icc (0:ℝ) t) := (huc.sub hvc).mono (Icc_subset_Icc_right ht.2)
    have hd0 : d 0 = 0 := by simpa [d] using heq 0 ⟨le_rfl,hT⟩
    let S := {s ∈ Icc (0:ℝ) t | d s = 0}
    have hS : IsCompact S := by
      have he : S = Icc (0:ℝ) t ∩ d ⁻¹' {0} := rfl
      refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _ h => h.1)
      rw [he, ← isClosed_Icc.inter_preimage_val_iff]
      exact isClosed_singleton.preimage hdc.restrict
    have hS0 : S.Nonempty := ⟨0, ⟨le_rfl,ht.1⟩,hd0⟩
    let z := sSup S
    have hz : IsGreatest S z := hS.isGreatest_sSup hS0
    have hz0 : 0 ≤ z := hz.1.1.1
    have hzt : z ≤ t := hz.1.1.2
    have hdz : d z = 0 := hz.1.2
    have hdPos (s : ℝ) (hs : s ∈ Icc z t) : 0 ≤ d s := by
      by_contra! hneg
      have h0s : 0 ≤ s := hz0.trans hs.1
      have hzs : z < s := lt_of_le_of_ne hs.1 (fun e => by subst s; linarith)
      have hmid := intermediate_value_Icc hs.2 (hdc.mono (Icc_subset_Icc_left h0s))
      obtain ⟨y, hy, hy0⟩ := hmid ⟨hneg.le,hdt.le⟩
      have hyn : y ∈ S := ⟨⟨h0s.trans hy.1,hy.2⟩,hy0⟩
      exact not_le_of_gt (hzs.trans_le hy.1) (hz.2 hyn)
    have hi (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 T) :
        IntervalIntegrable f volume 0 z ∧ IntervalIntegrable f volume z t :=
      ⟨hf.mono_set (by simp only [uIcc_of_le hz0,uIcc_of_le hT]; exact Icc_subset_Icc_right (hzt.trans ht.2)),
        hf.mono_set (by simp only [uIcc_of_le hzt,uIcc_of_le hT]; exact Icc_subset_Icc hz0 ht.2)⟩
    have he (s : ℝ) (hs : s ∈ Icc 0 T) :
        d s = ∫ r in (0:ℝ)..s, (R (v r) - R (u r)) := heq s hs
    have hiR := hi _ (hv.sub hu)
    have hadj := intervalIntegral.integral_add_adjacent_intervals hiR.1 hiR.2
    rw [← he z ⟨hz0,hzt.trans ht.2⟩, hdz, zero_add, ← he t ht] at hadj
    have hn : (∫ r in z..t, R (v r) - R (u r)) ≤ 0 := by
      have hh := intervalIntegral.integral_mono_on hzt hiR.2 (intervalIntegrable_const (c := (0:ℝ)))
        (fun s hs => sub_nonpos.mpr (hR (sub_nonneg.mp (hdPos s hs))))
      simpa using hh
    linarith
  have hrev (t : ℝ) (ht : t ∈ Icc 0 T) :
      v t - u t = ∫ s in (0:ℝ)..t, (R (u s) - R (v s)) := by
    have hh := congrArg (fun a : ℝ => -a) (heq t ht)
    rw [← intervalIntegral.integral_neg] at hh
    simpa only [neg_sub] using hh
  exact fun t ht => le_antisymm (less huc hvc hu hv heq t ht)
    (less hvc huc hv hu hrev t ht)

set_option maxHeartbeats 1000000 in
private theorem measurable_clock {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [StandardBorelSpace E]
    (T : ℝ) (hT : 0 ≤ T) (R : E → ℝ → ℝ)
    (hRM : Measurable (Function.uncurry R))
    (hR : ∀ b, Monotone (R b)) (K : ℝ)
    (hRB : ∀ b s, |R b s| ≤ K)
    (b : Ω → E) (hb : Measurable b)
    (a : Ω → Icc (0:ℝ) T → ℝ) (haM : ∀ t, Measurable (fun ω => a ω t))
    (r : Ω → C(Icc (0:ℝ) T,ℝ))
    (hr : ∀ ω (t : Icc (0:ℝ) T), r ω t = a ω t -
      ∫ s in (0:ℝ)..t.val, R (b ω) (r ω (Set.projIcc 0 T hT s))) :
    ∀ t : Icc (0:ℝ) T, Measurable (fun ω => r ω t) := by
  let F := C(Icc (0:ℝ) T,ℝ)
  letI : MeasurableSpace F := borel F
  letI : BorelSpace F := ⟨rfl⟩
  have hcl (t : Icc (0:ℝ) T) : Set.projIcc 0 T hT t = t := by
    apply Subtype.ext
    simp [Set.projIcc, max_eq_right t.2.1, min_eq_right t.2.2]
  let B (x : F) (s : ℝ) : ℝ := x (Set.projIcc 0 T hT s)
  have hB (x : F) : Continuous (B x) := x.continuous.comp continuous_projIcc
  have hBS : Measurable (Function.uncurry B) := by
    apply Continuous.measurable
    have hP : Continuous (Set.projIcc (0:ℝ) T hT) := continuous_projIcc
    exact continuous_eval.comp (continuous_fst.prodMk (hP.comp continuous_snd))
  let g (e : E) (x : F) (s : ℝ) : ℝ := R e (B x s)
  have hg : Measurable (fun q : (E × F) × ℝ => g q.1.1 q.1.2 q.2) :=
    hRM.comp (measurable_fst.fst.prodMk (hBS.comp (measurable_fst.snd.prodMk measurable_snd)))
  have hI (e : E) (x : F) : IntervalIntegrable (g e x) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact (integrable_const K).mono' (hRM.comp (measurable_const.prodMk (hB x).measurable)).aestronglyMeasurable
      (ae_of_all _ (fun s => by simpa [Real.norm_eq_abs] using hRB e (B x s)))
  let J (t : Icc (0:ℝ) T) (p : E × F) := ∫ s in (0:ℝ)..t.val, g p.1 p.2 s
  have hJm (t : Icc (0:ℝ) T) : Measurable (J t) := by
    simpa only [J, intervalIntegral.integral_of_le t.2.1, Function.uncurry_apply_pair] using
      (hg.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 t.val))).measurable
  have hJc (p : E × F) : Continuous (fun t : Icc (0:ℝ) T => J t p) := by
    have hj := intervalIntegral.continuousOn_primitive_interval' (hI p.1 p.2)
      (left_mem_uIcc (a := (0:ℝ)) (b := T))
    rw [uIcc_of_le hT] at hj
    exact hj.restrict
  obtain ⟨D, hD, hDense⟩ := TopologicalSpace.exists_countable_dense (Icc (0:ℝ) T)
  letI : Countable D := hD.to_subtype
  let E₁ := E × (D → ℝ)
  let tot (x : E₁ × F) (t : Icc (0:ℝ) T) := x.2 t + J t (x.1.1,x.2)
  let G : Set (E₁ × F) := ⋂ t : D, {p : E₁ × F | tot p t.val = p.1.2 t}
  have hG : MeasurableSet G :=
    MeasurableSet.iInter (fun t => measurableSet_eq_fun
      (((continuous_eval_const t.val).measurable.comp measurable_snd).add
        ((hJm _).comp (measurable_fst.fst.prodMk measurable_snd)))
      ((measurable_pi_apply t).comp measurable_fst.snd))
  have huniq {p : E₁} {u v : F} (hu : (p,u) ∈ G) (hv : (p,v) ∈ G) : u = v := by
    have hc : IsClosed {t : Icc (0:ℝ) T | tot (p,u) t = tot (p,v) t} :=
      isClosed_eq (u.continuous.add (hJc _)) (v.continuous.add (hJc _))
    have hsub : D ⊆ {t : Icc (0:ℝ) T | tot (p,u) t = tot (p,v) t} := by
      intro t ht
      exact (mem_iInter.1 hu ⟨t,ht⟩).trans (mem_iInter.1 hv ⟨t,ht⟩).symm
    have hh := closure_minimal hsub hc
    rw [hDense.closure_eq] at hh
    have hEq := scalar_monotone_clock_eq hT (R p.1) (B u) (B v) (hR p.1)
      (hB u).continuousOn (hB v).continuousOn (hI p.1 u) (hI p.1 v) (by
        intro t ht
        let tp : Icc (0:ℝ) T := ⟨t,ht⟩
        have hTe : tot (p,u) tp = tot (p,v) tp := hh (mem_univ tp)
        rw [intervalIntegral.integral_sub
          ((hI p.1 v).mono_set (by simpa only [uIcc_of_le ht.1,uIcc_of_le hT] using Icc_subset_Icc_right ht.2))
          ((hI p.1 u).mono_set (by simpa only [uIcc_of_le ht.1,uIcc_of_le hT] using Icc_subset_Icc_right ht.2))]
        have hpt : Set.projIcc 0 T hT t = tp := hcl tp
        simp only [tot,J,g,B,hpt,tp] at hTe ⊢
        linarith)
    ext t
    simpa only [B,hcl t] using hEq t.2
  let b₁ (ω : Ω) : E₁ := (b ω, fun t => a ω t.val)
  have hb₁ : Measurable b₁ :=
    hb.prodMk (measurable_pi_lambda _ (fun t => haM t.val))
  have hMem (ω : Ω) : (b₁ ω,r ω) ∈ G := by
    apply mem_iInter.2
    intro t
    change r ω t.val + J t.val (b ω,r ω) = a ω t.val
    rw [hr ω t.val]
    change (a ω t.val - J t.val (b ω,r ω)) + _ = _
    ring
  have hm := measurable_unique_graph_section G hG huniq b₁ hb₁ r hMem
  exact fun t => (continuous_eval_const t).measurable.comp hm

open scoped ENNReal
private noncomputable def clipped_clock_value (K : ℕ) (u : ℚ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨅ q : ℚ, if x < (q:ℝ) then min (K:ℝ≥0∞) (ENNReal.ofReal (u q)) else K

private noncomputable def clipped_clock (K : ℕ) (u : ℚ → ℝ) (x : ℝ) : ℝ :=
  (clipped_clock_value K u x).toReal

private theorem clipped_clock_value_le (K : ℕ) (u : ℚ → ℝ) (x : ℝ) :
    clipped_clock_value K u x ≤ (K:ℝ≥0∞) := by
  exact (iInf_le _ (0:ℚ)).trans (by split_ifs <;> simp)

private theorem clipped_clock_meas (K : ℕ) :
    Measurable (Function.uncurry (clipped_clock K)) := by
  apply ENNReal.measurable_toReal.comp
  unfold clipped_clock_value
  apply Measurable.iInf
  intro q
  exact (measurable_const.min ((measurable_pi_apply q).comp measurable_fst).ennreal_ofReal).ite
    (measurableSet_lt measurable_snd measurable_const) measurable_const

private theorem clipped_clock_mono (K : ℕ) (u : ℚ → ℝ) : Monotone (clipped_clock K u) := by
  intro x y hxy
  apply ENNReal.toReal_mono (ne_top_of_le_ne_top (ENNReal.natCast_ne_top K) (clipped_clock_value_le K u y))
  unfold clipped_clock_value
  apply le_iInf
  intro q
  refine (iInf_le _ q).trans ?_
  by_cases h : y < (q:ℝ)
  · rw [if_pos (hxy.trans_lt h), if_pos h]
  · rw [if_neg h]
    split_ifs <;> simp

private theorem clipped_clock_bdd (K : ℕ) (u : ℚ → ℝ) (x : ℝ) :
    |clipped_clock K u x| ≤ (K:ℝ) := by
  unfold clipped_clock
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top K) (clipped_clock_value_le K u x)

private theorem clipped_clock_eq_of_right_continuous (K : ℕ) (R : ℝ → ℝ)
    (hRn : ∀ s, 0 ≤ s → 0 ≤ R s) (hRm : MonotoneOn R (Ici 0))
    (hRc : ∀ t, 0 ≤ t → ContinuousWithinAt R (Ici t) t)
    (x : ℝ) (hx : 0 ≤ x) (hK : R x ≤ K) :
    clipped_clock K (fun q => R (q:ℝ)) x = R x := by
  let u (q : ℚ) := R (q:ℝ)
  have hle : ENNReal.ofReal (R x) ≤ clipped_clock_value K u x := by
    have hK' : ENNReal.ofReal (R x) ≤ (K:ℝ≥0∞) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hK
    apply le_iInf
    intro q
    by_cases hq : x < (q:ℝ)
    · rw [if_pos hq]
      exact le_min hK' (ENNReal.ofReal_le_ofReal (hRm hx (hx.trans hq.le) hq.le))
    · rwa [if_neg hq]
  apply le_antisymm
  · by_contra! hh
    obtain ⟨δ,hδ,hclose⟩ := Metric.continuousWithinAt_iff.1 (hRc x hx)
      ((clipped_clock K u x - R x)/2) (by linarith)
    obtain ⟨q,hq,hq'⟩ := exists_rat_btwn (lt_add_of_pos_right x hδ)
    have hd : dist (q:ℝ) x < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hq)]
      linarith
    have hc := hclose hq.le hd
    rw [Real.dist_eq] at hc
    have hbound : clipped_clock_value K u x ≤ ENNReal.ofReal (R (q:ℝ)) := by
      apply (iInf_le _ q).trans
      rw [if_pos hq]
      exact min_le_right _ _
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rw [ENNReal.toReal_ofReal (hRn _ (hx.trans hq.le))] at hreal
    change clipped_clock K u x ≤ R (q:ℝ) at hreal
    have hhalf := (abs_lt.mp hc).2
    linarith
  · have hreal := ENNReal.toReal_mono
      (ne_top_of_le_ne_top (ENNReal.natCast_ne_top K) (clipped_clock_value_le K u x)) hle
    simpa only [ENNReal.toReal_ofReal (hRn x hx), clipped_clock, u] using hreal

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal
private theorem arrival_prefix_index {e : ℕ → ℝ} {s : ℝ}
    (h0 : e 0 ≤ s) (hm : ∃ m, s < e m) :
    ∃ j : ℕ, e j ≤ s ∧ s < e (j + 1) := by
  let b := Nat.find hm
  have hb : s < e b := Nat.find_spec hm
  have hb_pos : 0 < b := by
    by_contra! hb0
    rw [Nat.eq_zero_of_le_zero hb0] at hb
    exact (not_lt_of_ge h0) hb
  let j := b - 1
  have hsucc : j + 1 = b := by dsimp [j]; omega
  have hj_lt : j < b := by omega
  exact ⟨j, le_of_not_gt (Nat.find_min hm hj_lt), hsucc ▸ (show s < e b from hb)⟩

private theorem renewal_eq_of_bracket {e : ℕ → ℝ} (he : Monotone e) {s : ℝ} {j : ℕ}
    (hj : e j ≤ s) (hj_succ : s < e (j + 1)) : renewalCount e s = j := by
  unfold renewalCount
  refine le_antisymm (iSup_le fun r => iSup_le fun hr => ?_) (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  have h : r ≤ j := by
    by_contra! hjr
    exact (not_lt_of_ge hr) (hj_succ.trans_le (he hjr))
  exact_mod_cast h

private theorem arrival_right_continuous {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (M.A n i ω) (Set.Ici t) t := by
  let e := M.arrivalEpoch n i ω
  let r := M.lamN n i
  have hr : 0 < r := M.lamN_pos n i
  have he (j : ℕ) : e j = partialSum (fun m => M.U i m ω) j / r := by
    simp [e, r, SystemSequence.arrivalEpoch, partialSum, Finset.sum_div]
  have hmono : StrictMono e := by
    apply strictMono_nat_of_lt_succ
    intro j
    have hj := M.U_pos i (j + 1) ω (by omega)
    rw [he, he]
    apply (div_lt_div_iff_of_pos_right hr).2
    unfold partialSum
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
    linarith
  have hz : e 0 = 0 := by simp [he, partialSum]
  have hcross : ∃ m : ℕ, t < e m := by
    have hh := ((tendsto_atTop.1 (M.U_finite i ω)) (t * r + 1)).exists
    obtain ⟨m, hm⟩ := hh
    refine ⟨m, ?_⟩
    rw [he, lt_div_iff₀ hr]
    linarith
  obtain ⟨j, hj, hsucc⟩ := arrival_prefix_index (hz ▸ ht) hcross
  have hc (s : ℝ) (hs : t ≤ s) (hs' : s < e (j + 1)) : M.A n i ω s = j := by
    simp [SystemSequence.A, ← show e = M.arrivalEpoch n i ω from rfl,
      renewal_eq_of_bracket hmono.monotone (hj.trans hs) hs']
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [self_mem_nhdsWithin (s := Set.Ici t),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hsucc)] with s hs hsu
  exact (hc s hs hsu).trans (hc t le_rfl hsucc).symm

private theorem clock_monotone {v : ℝ → ℝ}
    (hi : ∀ t, 0 ≤ t → IntervalIntegrable v volume 0 t)
    (hv : ∀ t, 0 ≤ t → 0 ≤ v t) :
    MonotoneOn (fun t => ∫ s in (0 : ℝ)..t, v s) (Set.Ici 0) := by
  intro a ha b hb hab
  have h := intervalIntegral.integral_add_adjacent_intervals (hi a ha)
    ((hi a ha).symm.trans (hi b hb))
  have hn := intervalIntegral.integral_nonneg (μ := volume) hab (fun s hs => hv s (ha.trans hs.1))
  linarith

private theorem clock_continuous_right {v : ℝ → ℝ}
    (hi : ∀ t, 0 ≤ t → IntervalIntegrable v volume 0 t) (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (fun t => ∫ s in (0 : ℝ)..t, v s) (Set.Ici t) t := by
  have htop : t < t + 1 := by linarith
  have hh : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, v s) (Set.Icc 0 (t + 1)) := by
    simpa only [Set.uIcc_of_le (show 0 ≤ t + 1 by linarith)] using
      intervalIntegral.continuousOn_primitive_interval' (hi (t + 1) (by linarith))
        (Set.left_mem_uIcc (a := (0 : ℝ)) (b := t + 1))
  exact (hh t ⟨ht, htop.le⟩).mono_of_mem_nhdsWithin (by
    filter_upwards [self_mem_nhdsWithin (s := Set.Ici t),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htop)] with s hs hu
    exact ⟨ht.trans hs, hu.le⟩)

private theorem state_right_continuous {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (X Ψ : Ω → ℝ → Fin k → ℝ)
    (h : M.IsControlled n X0 X Ψ) (ω : Ω) (i : Fin k) (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (fun s => X ω s i) (Set.Ici t) t := by
  have hiR (s : ℝ) (hs : 0 ≤ s) := (h.integrable ω i s hs).2
  have hiS (s : ℝ) (hs : 0 ≤ s) := (h.integrable ω i s hs).1
  have hRmono := clock_monotone hiR (fun s hs => h.phi_nonneg ω s i hs)
  have hSmono := clock_monotone hiS (fun s hs => h.psi_nonneg ω s i hs)
  have hR0 : 0 ≤ queueTime X Ψ ω i t :=
    intervalIntegral.integral_nonneg ht (fun s hs => h.phi_nonneg ω s i hs.1)
  have hS0 : 0 ≤ busyTime Ψ ω i t :=
    intervalIntegral.integral_nonneg ht (fun s hs => h.psi_nonneg ω s i hs.1)
  have hcR : ContinuousWithinAt (fun s => M.R n i ω (queueTime X Ψ ω i s)) (Set.Ici t) t :=
    ((M.R_poisson n i).cadlag ω).1 _ hR0 |>.comp (clock_continuous_right hiR t ht)
      (fun s hs => hRmono ht (ht.trans hs) hs)
  have hcS : ContinuousWithinAt (fun s => M.S n i ω (busyTime Ψ ω i s)) (Set.Ici t) t :=
    ((M.S_poisson n i).cadlag ω).1 _ hS0 |>.comp (clock_continuous_right hiS t ht)
      (fun s hs => hSmono ht (ht.trans hs) hs)
  have hh : ContinuousWithinAt
      (fun s => (X0 i : ℝ) + M.A n i ω s - M.R n i ω (queueTime X Ψ ω i s) -
        M.S n i ω (busyTime Ψ ω i s)) (Set.Ici t) t :=
    ((continuousWithinAt_const.add (arrival_right_continuous M n i ω t ht)).sub hcR).sub hcS
  exact hh.congr (fun s hs => h.eq7 ω s i (ht.trans hs)) (h.eq7 ω t i ht)

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
open scoped NNReal

private theorem path_above_bound {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
    ∃ j : ℕ, M.arrivalEpoch n i ω j ≤ t ∧ t < M.arrivalEpoch n i ω (j+1) := by
  have hz : M.arrivalEpoch n i ω 0 = 0 := by simp [SystemSequence.arrivalEpoch,partialSum]
  have hcross : ∃ m : ℕ, t < M.arrivalEpoch n i ω m := by
    obtain ⟨m, hm⟩ := ((tendsto_atTop.1 (M.U_finite i ω)) (t * M.lamN n i + 1)).exists
    refine ⟨m, ?_⟩
    simp only [SystemSequence.arrivalEpoch,partialSum,← Finset.sum_div]
    apply (lt_div_iff₀ (M.lamN_pos n i)).2
    unfold partialSum at hm
    linarith
  exact arrival_prefix_index (hz ▸ ht) hcross

private theorem arrival_epoch_strict {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) :
    StrictMono (M.arrivalEpoch n i ω) := by
  apply strictMono_nat_of_lt_succ
  intro j
  unfold SystemSequence.arrivalEpoch partialSum
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j+1)]
  exact lt_add_of_pos_right _ (div_pos (M.U_pos i (j+1) ω (by omega)) (M.lamN_pos n i))

private theorem arrival_measurable_of_nonnegative_time {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (fun ω => M.A n i ω t) := by
  let C (ω : Ω) : ℝ≥0∞ := ⨆ j : ℕ, if M.arrivalEpoch n i ω j ≤ t then (j:ℝ≥0∞) else 0
  have hC : Measurable C := by
    apply Measurable.iSup
    intro j
    have hE : Measurable (fun ω => M.arrivalEpoch n i ω j) :=
      Finset.measurable_sum (Finset.Icc 1 j) (fun m _ => (M.U_meas i m).div_const (M.lamN n i))
    exact measurable_const.ite (measurableSet_le hE measurable_const) measurable_const
  have he : (fun ω => M.A n i ω t) = fun ω => (C ω).toReal := by
    funext ω
    obtain ⟨j,hj,hj'⟩ := path_above_bound M n i ω t ht
    have hm := arrival_epoch_strict M n i ω
    have he : C ω = j := by
      apply le_antisymm
      · apply iSup_le
        intro l
        split_ifs with hl
        · have hl' : l ≤ j := by
            by_contra! h
            exact not_le_of_gt (hj'.trans_le (hm.monotone h)) hl
          exact_mod_cast hl'
        · exact zero_le
      · exact le_iSup_of_le j (by simp [hj])
    simp [SystemSequence.A, renewal_eq_of_bracket hm.monotone hj hj', he]
  rw [he]
  exact ENNReal.measurable_toReal.comp hC

private theorem arrival_mono {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) :
    MonotoneOn (M.A n i ω) (Ici 0) := by
  intro s hs t ht hst
  have hmono : renewalCount (M.arrivalEpoch n i ω) s ≤ renewalCount (M.arrivalEpoch n i ω) t :=
    iSup₂_le (fun j hj => le_iSup₂_of_le j (hj.trans hst) le_rfl)
  obtain ⟨j,hj,htj⟩ := path_above_bound M n i ω t ht
  have hct := renewal_eq_of_bracket (arrival_epoch_strict M n i ω).monotone hj htj
  have hneq : renewalCount (M.arrivalEpoch n i ω) t ≠ ⊤ := by rw [hct]; exact ENat.coe_ne_top _
  unfold SystemSequence.A
  exact_mod_cast ENat.toNat_le_toNat hmono hneq

private theorem joint_nnreal {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℝ → ℝ)
    (hm : ∀ t, 0 ≤ t → Measurable (fun ω => f ω t))
    (hr : ∀ ω t, 0 ≤ t → ContinuousWithinAt (f ω) (Ici t) t) :
    Measurable (fun z : Ω × ℝ≥0 => f z.1 z.2) := by
  have hh := AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
    (fun t ω => f ω t) (fun (t : ℝ≥0) => hm t t.2) (fun ω (t : ℝ≥0) =>
      ((hr ω t t.2).comp continuous_subtype_val.continuousWithinAt) (fun _ hs => hs))
  exact hh.comp measurable_swap

set_option maxHeartbeats 3200000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hSCP : M.IsSCP n X0 X Ψ) :
    Measurable (fun z : Ω × ℝ≥0 => X z.1 z.2) ∧
      Measurable (fun z : Ω × ℝ≥0 => Ψ z.1 z.2) := by
  have hC := hSCP.controlled
  have hΨ (i : Fin k) : Measurable (fun z : Ω × ℝ≥0 => Ψ z.1 z.2 i) :=
    joint_nnreal _ (fun t _ => hSCP.meas t i) (fun ω t ht => (hSCP.cadlag ω i).1 t ht)
  refine ⟨?_, measurable_pi_lambda _ hΨ⟩
  apply measurable_pi_lambda
  intro i
  refine joint_nnreal (fun ω t => X ω t i) ?_ ?_
  swap
  · exact fun ω t ht => state_right_continuous M n X0 X Ψ hC ω i t ht
  intro T hT
  have hA := joint_nnreal (M.A n i) (arrival_measurable_of_nonnegative_time M n i)
    (arrival_right_continuous M n i)
  have hS := joint_nnreal (M.S n i) (fun t _ => (M.S_poisson n i).meas t)
    (fun ω t ht => ((M.S_poisson n i).cadlag ω).1 t ht)
  have hR := joint_nnreal (M.R n i) (fun t _ => (M.R_poisson n i).meas t)
    (fun ω t ht => ((M.R_poisson n i).cadlag ω).1 t ht)
  let bus (ω : Ω) (t : ℝ) := busyTime Ψ ω i t
  let que (ω : Ω) (t : ℝ) := queueTime X Ψ ω i t
  have hb0 (ω : Ω) (s : ℝ) (hs : 0 ≤ s) : 0 ≤ bus ω s :=
    intervalIntegral.integral_nonneg hs (fun u hu => hC.psi_nonneg ω u i hu.1)
  have hq0 (ω : Ω) (s : ℝ) (hs : 0 ≤ s) : 0 ≤ que ω s :=
    intervalIntegral.integral_nonneg hs (fun u hu => hC.phi_nonneg ω u i hu.1)
  have hbM (t : ℝ) (ht : 0 ≤ t) : Measurable (fun ω => bus ω t) := by
    have hm := (hΨ i).comp (measurable_fst.prodMk measurable_snd.real_toNNReal :
      Measurable (fun z : Ω × ℝ => (z.1,z.2.toNNReal)))
    have hi := (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0:ℝ) t))).measurable
    convert hi using 1
    funext ω
    rw [show bus ω t = ∫ s in (0 : ℝ)..t, Ψ ω s i from rfl, intervalIntegral.integral_of_le ht]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    simp [Real.coe_toNNReal _ hs.1.le]
  have hbJ : Measurable (fun z : Ω × ℝ≥0 => bus z.1 z.2) :=
    joint_nnreal _ hbM (fun ω t ht =>
      clock_continuous_right (fun u hu => (hC.integrable ω i u hu).1) t ht)
  let a (ω : Ω) (s : ℝ) : ℝ :=
    (X0 i:ℝ) + M.A n i ω s - M.S n i ω (bus ω s) - Ψ ω s i
  have haMeas : Measurable (fun z : Ω × ℝ => a z.1 z.2.toNNReal) := by
    let p (z : Ω × ℝ) : Ω × ℝ≥0 := (z.1,z.2.toNNReal)
    have hp : Measurable p := measurable_fst.prodMk measurable_snd.real_toNNReal
    have hq : Measurable (fun z : Ω × ℝ≥0 => M.S n i z.1 (bus z.1 z.2)) := by
      have hm := hS.comp (measurable_fst.prodMk hbJ.real_toNNReal)
      convert hm using 1
      funext z
      simp [Real.coe_toNNReal _ (hb0 z.1 z.2 z.2.2)]
    exact (((hA.comp hp).const_add _).sub (hq.comp hp)).sub ((hΨ i).comp hp)
  have hAR (ω : Ω) (s : ℝ) (hs : 0 ≤ s) :
      a ω s = (X ω s i - Ψ ω s i) + M.R n i ω (que ω s) := by
    unfold a
    have he := hC.eq7 ω s i hs
    dsimp [bus,que]
    linarith
  have hRn (ω : Ω) (s : ℝ) (hs : 0 ≤ s) : 0 ≤ M.R n i ω s := by
    rw [← (M.R_poisson n i).zero ω]
    exact (M.R_poisson n i).mono ω (mem_Ici.2 le_rfl) (mem_Ici.2 hs) hs
  have hSn (ω : Ω) (s : ℝ) (hs : 0 ≤ s) : 0 ≤ M.S n i ω s := by
    rw [← (M.S_poisson n i).zero ω]
    exact (M.S_poisson n i).mono ω (mem_Ici.2 le_rfl) (mem_Ici.2 hs) hs
  have haB (ω : Ω) (s : ℝ) (hs : s ∈ Icc 0 T) :
      M.R n i ω (que ω s) ≤ a ω s ∧ a ω s ≤ (X0 i:ℝ) + M.A n i ω T := by
    constructor
    · rw [hAR ω s hs.1]
      exact le_add_of_nonneg_left (hC.phi_nonneg ω s i hs.1)
    · have hh := arrival_mono M n i ω hs.1 hT hs.2
      have h1 := hSn ω (bus ω s) (hb0 ω s hs.1)
      have h2 := hC.psi_nonneg ω s i hs.1
      unfold a
      linarith
  have haIntM (t : ℝ) (ht : 0 ≤ t) : Measurable (fun ω => ∫ s in (0:ℝ)..t, a ω s) := by
    have hi := (haMeas.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0:ℝ) t))).measurable
    convert hi using 1
    funext ω
    rw [intervalIntegral.integral_of_le ht]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    simp only [Real.coe_toNNReal _ hs.1.le]
  let E (K : ℕ) : Set Ω := {ω | (X0 i:ℝ) + M.A n i ω T ≤ K}
  have hEm (K : ℕ) : MeasurableSet (E K) := measurableSet_le
    ((arrival_measurable_of_nonnegative_time M n i T hT).const_add _) measurable_const
  have hqMloc (K : ℕ) : Measurable (fun ω : E K => que ω T) := by
    let b (ω : E K) (q : ℚ) := M.R n i ω (q:ℝ)
    have hb : Measurable b := measurable_pi_lambda _ (fun q =>
      ((M.R_poisson n i).meas q).comp measurable_subtype_coe)
    have hcont (ω : E K) : ContinuousOn (que ω) (Icc 0 T) := by
      simpa only [uIcc_of_le hT,que,queueTime] using
        intervalIntegral.continuousOn_primitive_interval' (hC.integrable ω i T hT).2
          (left_mem_uIcc (a := (0:ℝ)) (b := T))
    let Q (ω : E K) : C(Icc (0:ℝ) T,ℝ) := ⟨fun t => que ω t, (hcont ω).restrict⟩
    have hEq (ω : E K) (t : Icc (0:ℝ) T) :
        Q ω t = (∫ s in (0:ℝ)..t.val, a ω s) -
          ∫ s in (0:ℝ)..t.val, clipped_clock K (b ω) (Q ω (Set.projIcc 0 T hT s)) := by
      have hclip (s : ℝ) (hs : s ∈ Icc 0 T) :
          clipped_clock K (b ω) (Q ω (Set.projIcc 0 T hT s)) = M.R n i ω (que ω s) := by
        have ht : (Set.projIcc 0 T hT s : ℝ) = s := by
          simp [Set.projIcc, max_eq_right hs.1, min_eq_right hs.2]
        change clipped_clock K (b ω) (que ω (Set.projIcc 0 T hT s)) = _
        rw [ht]
        exact clipped_clock_eq_of_right_continuous K (M.R n i ω) (hRn ω)
          ((M.R_poisson n i).mono ω) ((M.R_poisson n i).cadlag ω).1 _ (hq0 ω s hs.1)
          ((haB ω s hs).1.trans ((haB ω s hs).2.trans ω.2))
      have hRI : IntervalIntegrable (fun s => clipped_clock K (b ω) (Q ω (Set.projIcc 0 T hT s)))
          volume 0 t.val := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le t.2.1]
        have hproj : Continuous (Set.projIcc (0:ℝ) T hT) := continuous_projIcc
        have hpair : Measurable (fun s : ℝ => (b ω, Q ω (Set.projIcc 0 T hT s))) :=
          measurable_const.prodMk ((Q ω).continuous.comp hproj).measurable
        have hm := (clipped_clock_meas K).comp hpair
        exact (integrable_const (K:ℝ)).mono' hm.aestronglyMeasurable
          (ae_of_all _ (fun s => by
            simpa [Real.norm_eq_abs] using
              (clipped_clock_bdd K (b ω) (Q ω (Set.projIcc 0 T hT s)))))
      have haI : IntervalIntegrable (a ω) volume 0 t.val := by
        let f (s : ℝ) := (X ω s i - Ψ ω s i) +
          clipped_clock K (b ω) (Q ω (Set.projIcc 0 T hT s))
        have hf : IntervalIntegrable f volume 0 t.val :=
          (hC.integrable ω i t.val t.2.1).2.add hRI
        have he : EqOn f (a ω) (uIoc 0 t.val) := by
          intro s hs
          rw [uIoc_of_le t.2.1] at hs
          have hst : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans t.2.2⟩
          unfold f
          rw [hclip s hst, hAR ω s hs.1.le]
        exact (intervalIntegrable_congr he).mp hf
      rw [← intervalIntegral.integral_sub haI hRI]
      change queueTime X Ψ ω i t = _
      unfold queueTime
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le t.2.1] at hs
      have ht : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans t.2.2⟩
      change X ω s i - Ψ ω s i = a ω s - clipped_clock K (b ω) (Q ω (Set.projIcc 0 T hT s))
      rw [hclip s ht, hAR ω s hs.1, add_sub_cancel_right]
    exact measurable_clock T hT (clipped_clock K) (clipped_clock_meas K) (clipped_clock_mono K)
      K (clipped_clock_bdd K) b hb (fun ω t => ∫ s in (0:ℝ)..t.val, a ω s)
      (fun t => (haIntM t t.2.1).comp measurable_subtype_coe) Q hEq ⟨T,hT,le_rfl⟩
  have hqM : Measurable (fun ω => que ω T) := by
    intro s hs
    have he : {ω | que ω T ∈ s} = ⋃ K : ℕ,
        ((↑) : E K → Ω) '' {ω : E K | que ω T ∈ s} := by
      ext ω
      constructor
      · intro hω
        obtain ⟨K,hK⟩ := exists_nat_ge ((X0 i:ℝ)+ M.A n i ω T)
        exact mem_iUnion.2 ⟨K,⟨⟨ω,hK⟩,hω,rfl⟩⟩
      · rintro h
        obtain ⟨K,ω',hω',rfl⟩ := mem_iUnion.1 h
        exact hω'
    change MeasurableSet {ω | que ω T ∈ s}
    rw [he]
    exact MeasurableSet.iUnion fun K => (MeasurableEmbedding.subtype_coe (hEm K)).measurableSet_image.2 (hqMloc K hs)
  have hmeas := (((hA.comp (measurable_id.prodMk (measurable_const (a := (⟨T,hT⟩:ℝ≥0))))).const_add (X0 i:ℝ)).sub
    (hR.comp (measurable_id.prodMk hqM.real_toNNReal))).sub
      (hS.comp (measurable_id.prodMk ((hbM T hT).real_toNNReal)))
  convert hmeas using 1
  funext ω
  change X ω T i = (X0 i:ℝ) + M.A n i ω T -
    M.R n i ω (que ω T).toNNReal - M.S n i ω (bus ω T).toNNReal
  simpa only [Real.coe_toNNReal _ (hb0 ω T hT), Real.coe_toNNReal _ (hq0 ω T hT), bus,que] using
    (hC.eq7 ω T i hT)
