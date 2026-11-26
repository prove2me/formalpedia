-- Prove2me | solution 1 for ManyServerQED.Scheduling.coupling_transfers_weighted_path_lipschitz_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:43:34.480966+00:00
-- url     : https://prove2.me/submissions/9ea1679a-2226-4b21-90fc-aa91e94747cb

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_measurable_compact_supremum_of_evaluation_path
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem irr_to_rational_weighted_bounds {E : Type*} [NormedAddCommGroup E]
    (A : ℝ → E) (R : ℝ → ℝ)
    (hA : ∀ t, 0 ≤ t → ContinuousWithinAt A (Ici t) t)
    (hR : ∀ t, 0 ≤ t → ContinuousWithinAt R (Ici t) t)
    (h : ∀ (s t : ℚ) (C : ℝ), 0 ≤ (s:ℝ) → (s:ℝ) ≤ t →
      (∀ u ∈ Icc (s:ℝ) (t:ℝ), R u ≤ C) → ‖A t-A s‖ ≤ C*((t:ℝ)-s)) :
    ∀ s t C, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, R u ≤ C) →
      ‖A t-A s‖ ≤ C*(t-s) := by
  intro s t C hs hst hC
  rcases hst.eq_or_lt with he | hst
  · subst t
    simp
  obtain ⟨p,_,hp,hpT⟩ := Real.exists_seq_rat_strictAnti_tendsto s
  obtain ⟨q,_,hq,hqT⟩ := Real.exists_seq_rat_strictAnti_tendsto t
  have hPT : Tendsto (fun n => (p n:ℝ)) atTop (𝓝[Ici s] s) :=
    tendsto_nhdsWithin_iff.2 ⟨hpT,Eventually.of_forall fun n => (hp n).le⟩
  have hQT : Tendsto (fun n => (q n:ℝ)) atTop (𝓝[Ici t] t) :=
    tendsto_nhdsWithin_iff.2 ⟨hqT,Eventually.of_forall fun n => (hq n).le⟩
  have hS := (hA s hs).tendsto.comp hPT
  have hT := (hA t (hs.trans hst.le)).tendsto.comp hQT
  have hOrd := tendsto_order.1 hpT |>.2 t hst
  have hε (ε : ℝ) (he : 0 < ε) : ‖A t-A s‖ ≤ (C+ε)*(t-s) := by
    obtain ⟨δ,hδ,hR'⟩ := Metric.continuousWithinAt_iff.1 (hR t (hs.trans hst.le)) ε he
    have hqq : ∀ᶠ n in atTop, (q n:ℝ) < t+δ :=
      (tendsto_order.1 hqT).2 _ (lt_add_of_pos_right _ hδ)
    refine le_of_tendsto_of_tendsto (hT.sub hS).norm
      (tendsto_const_nhds.mul (hqT.sub hpT)) ?_
    filter_upwards [hOrd,hqq] with n hn hnq
    apply h (p n) (q n) (C+ε) (hs.trans (hp n).le) (hn.le.trans (hq n).le)
    intro u hu
    by_cases hu' : u ≤ t
    · exact (hC u ⟨(hp n).le.trans hu.1,hu'⟩).trans (by linarith)
    · have hd : dist u t < δ := by
        rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.2 (le_of_not_ge hu'))]
        linarith [hu.2]
      have hR'' := hR' (le_of_not_ge hu') hd
      rw [Real.dist_eq] at hR''
      linarith [(abs_lt.1 hR'').2,hC t ⟨hst.le,le_rfl⟩]
  by_contra! h'
  let ε := (‖A t-A s‖-C*(t-s))/(2*(t-s))
  have he : 0 < ε := div_pos (sub_pos.2 h') (by linarith)
  have hh := hε ε he
  have hEq : ε*(t-s) = (‖A t-A s‖-C*(t-s))/2 := by
    dsimp [ε]
    field_simp [sub_ne_zero.2 hst.ne']
  rw [add_mul,hEq] at hh
  linarith

set_option maxHeartbeats 2250000 in
theorem solution {Ω E : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) (hs : Tendsto s atTop atTop)
    (A : (Fin (k+k+k+2) → ℝ) → E) (hA : Continuous A)
    (R : (Fin (k+k+k+2) → ℝ) → ℝ) (hR : Continuous R) (hRn : ∀ z, 0 ≤ R z)
    (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ x y, |R x-R y| ≤ L*∑ i, |x i-y i|)
    (hOrig : ∀ᶠ n in atTop, ∀ ω,
      (∀ t, 0 ≤ t → ContinuousWithinAt (Z n ω) (Ici t) t) ∧
      ∀ s t C, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, R (Z n ω u) ≤ C) →
        ‖A (Z n ω t)-A (Z n ω s)‖ ≤ C*(t-s)) :
    (∀ᵐ ω ∂d.Q, ∀ᶠ n in atTop, ∀ s t C, 0 ≤ s → s ≤ t →
      (∀ u ∈ Icc s t, R (d.row n ω u) ≤ C) →
        ‖A (d.row n ω t)-A (d.row n ω s)‖ ≤ C*(t-s)) ∧
    (∀ᵐ ω ∂d.Q, ∀ s t C, 0 ≤ s → s ≤ t →
      (∀ u ∈ Icc s t, R (d.limit ω u) ≤ C) →
        ‖A (d.limit ω t)-A (d.limit ω s)‖ ≤ C*(t-s)) := by
  classical
  let D := Fin (k+k+k+2) → ℝ
  let H := ℝ≥0 → D
  have hSExist (u : ℝ≥0) := measurable_compact_supremum_of_evaluation_path R hR u
  choose S hSm hS using hSExist
  let J (a b : ℚ) (p : H) :=
    S ((b:ℝ)-(a:ℝ)).toNNReal (fun t => p ((a:ℝ).toNNReal+t))
  have hJ (a b : ℚ) : Measurable (J a b) :=
    (hSm _).comp (measurable_pi_lambda _ (fun t => measurable_pi_apply _))
  have hJE (f : ℝ → D) (hf : ∀ t, 0 ≤ t → ContinuousWithinAt f (Ici t) t)
      (a b : ℚ) (ha : 0 ≤ (a:ℝ)) (hb : (a:ℝ) ≤ b) :
      J a b (fun t : ℝ≥0 => f t) =
        ⨆ u : Icc (a:ℝ) (b:ℝ), ENNReal.ofReal (R (f u.1)) := by
    let v (u : ℝ) := f ((a:ℝ)+u)
    have hv (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt v (Ici t) t :=
      (hf ((a:ℝ)+t) (add_nonneg ha ht)).comp (continuous_const.add continuous_id).continuousWithinAt
        (fun s hs => add_le_add_right (show t ≤ s from hs) _)
    have hv' : (fun t : ℝ≥0 => v t) = (fun t : ℝ≥0 => f (((a:ℝ).toNNReal+t:ℝ≥0):ℝ)) := by
      funext t
      rw [NNReal.coe_add,Real.coe_toNNReal _ ha]
    unfold J
    rw [← hv',hS _ v hv,Real.coe_toNNReal _ (sub_nonneg.2 hb)]
    apply le_antisymm
    · apply iSup₂_le
      intro u hu
      have h' : (a:ℝ)+u ∈ Icc (a:ℝ) (b:ℝ) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
      exact le_iSup (fun x : Icc (a:ℝ) (b:ℝ) => ENNReal.ofReal (R (f x.1))) ⟨_,h'⟩
    · apply iSup_le
      intro u
      have h' : (u:ℝ)-(a:ℝ) ∈ Icc (0:ℝ) ((b:ℝ)-(a:ℝ)) :=
        ⟨sub_nonneg.2 u.2.1,sub_le_sub_right u.2.2 _⟩
      have he : ENNReal.ofReal (R (v ((u:ℝ)-(a:ℝ)))) ≤
          ⨆ x : ℝ, ⨆ (_ : x ∈ Icc (0:ℝ) ((b:ℝ)-(a:ℝ))), ENNReal.ofReal (R (v x)) :=
        le_iSup₂_of_le ((u:ℝ)-(a:ℝ)) h' le_rfl
      simpa [v,add_sub_cancel] using he
  let U (a b : ℚ) (p : H) := ‖A (p ((b:ℝ).toNNReal))-A (p ((a:ℝ).toNNReal))‖
  have hUm (a b : ℚ) : Measurable (U a b) := by
    let z (p : H) := (p ((b:ℝ).toNNReal),p ((a:ℝ).toNNReal))
    have hz : Measurable z := (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    have h : Continuous (fun p : D × D => ‖A p.1-A p.2‖) :=
      ((hA.comp continuous_fst).sub (hA.comp continuous_snd)).norm
    exact h.measurable.comp hz
  let good (p : H) : Prop := ∀ (a b : ℚ),
    0 ≤ (a:ℝ) → (a:ℝ) ≤ b → J a b p ≠ ⊤ →
      U a b p ≤ (J a b p).toReal*((b:ℝ)-(a:ℝ))
  have hgood : MeasurableSet {p | good p} := by
    simp only [good,Set.setOf_forall]
    apply MeasurableSet.iInter
    intro a
    apply MeasurableSet.iInter
    intro b
    apply MeasurableSet.iInter
    intro ha
    apply MeasurableSet.iInter
    intro hab
    have he : {p | J a b p ≠ ⊤ → U a b p ≤ (J a b p).toReal*((b:ℝ)-(a:ℝ))} =
        (J a b ⁻¹' {⊤}) ∪ {p | U a b p ≤ (J a b p).toReal*((b:ℝ)-(a:ℝ))} := by
      ext p
      simp [not_imp_not,imp_iff_not_or]
    rw [he]
    exact ((measurableSet_singleton _).preimage (hJ a b)).union
      (measurableSet_le (hUm a b) ((hJ a b).ennreal_toReal.mul_const _))
  have hRaw : ∀ᶠ n in atTop, ∀ ω, good (fun t : ℝ≥0 => Z n ω t) := by
    filter_upwards [hOrig] with n h ω
    intro a b ha hab hs
    have hF := hJE (Z n ω) (h ω).1 a b ha hab
    have hh (u : ℝ) (hu : u ∈ Icc (a:ℝ) (b:ℝ)) :
        R (Z n ω u) ≤ (J a b (fun t : ℝ≥0 => Z n ω t)).toReal := by
      apply (ENNReal.ofReal_le_iff_le_toReal hs).1
      rw [hF]
      exact le_iSup (fun x : Icc (a:ℝ) (b:ℝ) => ENNReal.ofReal (R (Z n ω x.1))) ⟨u,hu⟩
    simpa only [U,Real.coe_toNNReal _ ha,Real.coe_toNNReal _ (ha.trans hab)] using
      (h ω).2 a b _ ha hab hh
  obtain ⟨N,hN⟩ := eventually_atTop.1 (d.row_law.and ((hs.comp d.r_cofinal).eventually hRaw))
  have hG (n : ℕ) : ∀ᵐ ω ∂d.Q, N ≤ n → good (fun t : ℝ≥0 => d.row n ω t) := by
    by_cases hn : N ≤ n
    · have h := (hN n hn).1.measure_mem_eq hgood.compl
      have h' : {ω | ¬good (fun t : ℝ≥0 => Z (s (d.r n)) ω t)} = ∅ :=
        eq_empty_iff_forall_notMem.2 (fun ω hw => hw ((hN n hn).2 ω))
      change d.Q {ω | ¬good (fun t : ℝ≥0 => d.row n ω t)} =
        P {ω | ¬good (fun t : ℝ≥0 => Z (s (d.r n)) ω t)} at h
      rw [h',measure_empty] at h
      simpa only [hn,true_implies] using (ae_iff.2 h)
    · exact Eventually.of_forall (fun ω h => (hn h).elim)
  have hRows : ∀ᵐ ω ∂d.Q, ∀ᶠ n in atTop, ∀ s t C, 0 ≤ s → s ≤ t →
      (∀ u ∈ Icc s t, R (d.row n ω u) ≤ C) →
        ‖A (d.row n ω t)-A (d.row n ω s)‖ ≤ C*(t-s) := by
    filter_upwards [ae_all_iff.2 hG] with ω hw
    filter_upwards [eventually_ge_atTop N] with n hn
    have hr (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt (d.row n ω) (Ici t) t :=
      continuousWithinAt_pi.2 (fun i => (d.row_cadlag n ω i).1 t ht)
    apply irr_to_rational_weighted_bounds _ _ (fun t ht => hA.continuousAt.comp_continuousWithinAt (hr t ht))
      (fun t ht => hR.continuousAt.comp_continuousWithinAt (hr t ht))
    intro a b C ha hab hC
    have hC0 : 0 ≤ C := (hRn _).trans (hC a ⟨le_rfl,hab⟩)
    have hJC : J a b (fun t : ℝ≥0 => d.row n ω t) ≤ ENNReal.ofReal C := by
      rw [hJE _ hr a b ha hab]
      exact iSup_le (fun u => ENNReal.ofReal_le_ofReal (hC u u.2))
    have hJf := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hJC
    have hJr := (ENNReal.toReal_le_toReal hJf ENNReal.ofReal_ne_top).2 hJC
    rw [ENNReal.toReal_ofReal hC0] at hJr
    have hh := hw n hn a b ha hab hJf
    rw [show U a b (fun t : ℝ≥0 => d.row n ω t) =
        ‖A (d.row n ω b)-A (d.row n ω a)‖ from by
          simp only [U,Real.coe_toNNReal _ ha,Real.coe_toNNReal _ (ha.trans hab)]] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hJr (sub_nonneg.2 hab))
  refine ⟨hRows,?_⟩
  filter_upwards [hRows,d.convergence] with ω hrow hconv
  intro s t C hs hst hC
  have ht := hs.trans hst
  have hEv (u : ℝ) (hu : u ∈ Icc (0:ℝ) t) :
      Tendsto (fun n => d.row n ω u) atTop (𝓝 (d.limit ω u)) := by
    apply tendsto_pi_nhds.2
    intro i
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [(tendsto_order.1 (hconv t ht)).2 _ (ENNReal.ofReal_pos.2 hε)] with n hn
    rw [Real.dist_eq]
    have hSum := Finset.single_le_sum
      (f := fun i => |d.row n ω u i-d.limit ω u i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    exact (ENNReal.ofReal_lt_ofReal_iff hε).1 (lt_of_le_of_lt
      ((ENNReal.ofReal_le_ofReal hSum).trans (le_iSup₂_of_le u hu le_rfl)) hn)
  have hDr := ((hA.continuousAt.tendsto.comp (hEv t ⟨ht,le_rfl⟩)).sub
    (hA.continuousAt.tendsto.comp (hEv s ⟨hs,hst⟩))).norm
  have hδ (ε : ℝ) (he : 0 < ε) :
      ‖A (d.limit ω t)-A (d.limit ω s)‖ ≤ (C+ε)*(t-s) := by
    let η := ε/(L+1)
    have hη : 0 < η := by dsimp [η]; positivity
    refine le_of_tendsto hDr ?_
    filter_upwards [hrow,(tendsto_order.1 (hconv t ht)).2 _ (ENNReal.ofReal_pos.2 hη)] with n hn hn'
    refine hn s t (C+ε) hs hst (fun u hu => ?_)
    have hsum : ∑ i, |d.row n ω u i-d.limit ω u i| < η :=
      (ENNReal.ofReal_lt_ofReal_iff hη).1 ((le_iSup₂_of_le u ⟨hs.trans hu.1,hu.2⟩ le_rfl).trans_lt hn')
    have hErr := hLip (d.row n ω u) (d.limit ω u)
    have hm := mul_le_mul_of_nonneg_left hsum.le hL
    have he : L*η ≤ ε := by
      dsimp [η]
      calc
        _ ≤ (L+1)*(ε/(L+1)) := mul_le_mul_of_nonneg_right (by linarith) hη.le
        _ = ε := by field_simp [show (L+1) ≠ 0 by positivity]
    linarith [(abs_le.1 (hErr.trans (hm.trans he))).2,hC u hu]
  have hε (j : ℕ) : 0 < 1/((j:ℝ)+1) := by positivity
  have hT : Tendsto (fun j : ℕ => (C+1/((j:ℝ)+1))*(t-s)) atTop (𝓝 (C*(t-s))) := by
    have h : Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop).atTop_add
      tendsto_const_nhds : Tendsto (fun j : ℕ => (j:ℝ)+1) atTop atTop)
    simpa only [add_zero] using (tendsto_const_nhds.add h).mul_const (t-s)
  exact ge_of_tendsto' hT (fun j => hδ _ (hε j))
