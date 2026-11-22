-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianPositiveBarrierStationaryIncrementV1
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T18:48:48.512388+00:00
-- url     : https://prove2.me/submissions/7467aa28-82a6-4575-bf09-f5dabea28295

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstUpperPassageAlmostSureFinitePublic
import Theorems.Thm_Kyprianou_Ch01_zeroBoundaryPassageClockMeasurableV1

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

set_option autoImplicit false

section StrongMarkovEngine

private lemma firstUpperPassage_lt_iff_rat
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hCont : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) (t : ℝ≥0) (ω : Ω) :
    Kyprianou.Ch01.firstUpperPassage X s ω < (t : WithTop ℝ≥0) ↔
      ∃ q : {q : ℚ // 0 < q ∧ (q : ℝ) < (t : ℝ)},
        s < X ⟨(q.1 : ℝ), by exact_mod_cast q.2.1.le⟩ ω := by
  classical
  dsimp only [Kyprianou.Ch01.firstUpperPassage]
  constructor
  · intro hlt
    split_ifs at hlt with hex
    · have hInf_lt : sInf ({u : ℝ≥0 | 0 < u ∧ s < X u ω} : Set ℝ≥0) < t :=
        WithTop.coe_lt_coe.mp hlt
      have hne : ({u : ℝ≥0 | 0 < u ∧ s < X u ω} : Set ℝ≥0).Nonempty := hex
      obtain ⟨u, ⟨hu_pos, hXu⟩, hu_lt⟩ := (csInf_lt_iff (OrderBot.bddBelow _) hne).mp hInf_lt
      have hOpen : IsOpen {r : ℝ≥0 | s < X r ω} := isOpen_lt continuous_const (hCont ω)
      have hNhds : {r : ℝ≥0 | s < X r ω} ∈ 𝓝 u := hOpen.mem_nhds hXu
      rw [Metric.mem_nhds_iff] at hNhds
      obtain ⟨δ, hδ_pos, hδ⟩ := hNhds
      have hHi : (u : ℝ) < min (t : ℝ) ((u : ℝ) + δ) :=
        lt_min (NNReal.coe_lt_coe.mpr hu_lt) (by linarith)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hHi
      have hq_pos : (0 : ℚ) < q := by
        exact_mod_cast lt_trans (NNReal.coe_pos.mpr hu_pos) hq1
      have hq_lt_t : (q : ℝ) < (t : ℝ) := lt_of_lt_of_le hq2 (min_le_left _ _)
      let rq : ℝ≥0 := ⟨(q : ℝ), by exact_mod_cast hq_pos.le⟩
      have hq_mem : rq ∈ Metric.ball u δ := by
        rw [Metric.mem_ball, NNReal.dist_eq]
        change |(q : ℝ) - (u : ℝ)| < δ
        rw [abs_of_pos (sub_pos.mpr hq1)]
        have hq_lt_d : (q : ℝ) < (u : ℝ) + δ := lt_of_lt_of_le hq2 (min_le_right _ _)
        linarith
      exact ⟨⟨q, hq_pos, hq_lt_t⟩, hδ hq_mem⟩
    · exact absurd hlt not_top_lt
  · rintro ⟨⟨q, hq_pos, hq_lt_t⟩, hXq⟩
    have hq_nn : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pos.le
    let r : ℝ≥0 := ⟨(q : ℝ), hq_nn⟩
    have hr_pos : 0 < r := NNReal.coe_pos.mp (show (0 : ℝ) < (q : ℝ) by exact_mod_cast hq_pos)
    have hr_lt : r < t := NNReal.coe_lt_coe.mp hq_lt_t
    have hex : ∃ u : ℝ≥0, 0 < u ∧ s < X u ω := ⟨r, hr_pos, hXq⟩
    rw [if_pos hex]
    exact WithTop.coe_lt_coe.mpr (lt_of_le_of_lt (csInf_le (OrderBot.bddBelow _) ⟨hr_pos, hXq⟩) hr_lt)

private lemma measurableSet_firstUpperPassage_lt_naturalSigma
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hCont : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) (t : ℝ≥0) :
    @MeasurableSet Ω (Kyprianou.Ch01.naturalSigma X t)
      {ω | Kyprianou.Ch01.firstUpperPassage X s ω < (t : WithTop ℝ≥0)} := by
  letI : MeasurableSpace Ω := Kyprianou.Ch01.naturalSigma X t
  have hEq : {ω | Kyprianou.Ch01.firstUpperPassage X s ω < (t : WithTop ℝ≥0)} =
      ⋃ q : {q : ℚ // 0 < q ∧ (q : ℝ) < (t : ℝ)},
        {ω | s < X ⟨(q.1 : ℝ), by exact_mod_cast q.2.1.le⟩ ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact firstUpperPassage_lt_iff_rat X hCont s t ω
  rw [hEq]
  refine MeasurableSet.iUnion fun q => ?_
  let r : ℝ≥0 := ⟨(q.1 : ℝ), by exact_mod_cast q.2.1.le⟩
  have hr_le : r ≤ t := NNReal.coe_le_coe.mp q.2.2.le
  have hle : MeasurableSpace.comap (X r) inferInstance ≤ Kyprianou.Ch01.naturalSigma X t :=
    le_iSup₂_of_le r hr_le le_rfl
  exact hle _ ⟨Set.Ioi s, measurableSet_Ioi, rfl⟩

private lemma firstUpperPassage_val_and_shift
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hCont : Continuous (fun t : ℝ≥0 => X t ω))
    (h0 : X 0 ω = 0)
    (s : ℝ) (hs : 0 < s) (τ : ℝ≥0)
    (hτ : Kyprianou.Ch01.firstUpperPassage X s ω = (τ : WithTop ℝ≥0)) :
    (∀ u : ℝ≥0, u ≤ τ → X u ω ≤ s) ∧ X τ ω = s ∧
      ∀ h : ℝ, 0 < h →
        Kyprianou.Ch01.firstUpperPassage X (s + h) ω =
          (τ : WithTop ℝ≥0) +
            Kyprianou.Ch01.firstUpperPassage (fun u ω' => X (τ + u) ω' - X τ ω') h ω := by
  classical
  have hex : ∃ t : ℝ≥0, 0 < t ∧ s < X t ω := by
    by_contra hno
    dsimp only [Kyprianou.Ch01.firstUpperPassage] at hτ
    rw [if_neg hno] at hτ
    exact WithTop.top_ne_coe hτ
  have hτ_eq : sInf ({t : ℝ≥0 | 0 < t ∧ s < X t ω} : Set ℝ≥0) = τ := by
    dsimp only [Kyprianou.Ch01.firstUpperPassage] at hτ
    rw [if_pos hex] at hτ
    exact WithTop.coe_eq_coe.mp hτ
  have hle_lt : ∀ u : ℝ≥0, u < τ → X u ω ≤ s := fun u hu => by
    by_cases hu0 : u = 0
    · subst hu0; rw [h0]; exact hs.le
    · by_contra hgt
      have hmem : u ∈ {t : ℝ≥0 | 0 < t ∧ s < X t ω} := ⟨pos_iff_ne_zero.mpr hu0, lt_of_not_ge hgt⟩
      have hle : τ ≤ u := by rw [← hτ_eq]; exact csInf_le (OrderBot.bddBelow _) hmem
      exact not_lt_of_ge hle hu
  have hXτ_le : X τ ω ≤ s := by
    by_cases hτ0 : τ = 0
    · subst hτ0; rw [h0]; exact hs.le
    · have hτ_pos : 0 < τ := pos_iff_ne_zero.mpr hτ0
      have hLim : Tendsto (fun n : ℕ => X (τ * (1 - 1 / ((n : ℝ≥0) + 2))) ω) atTop (𝓝 (X τ ω)) := by
        have hseq : Tendsto (fun n : ℕ => τ * (1 - 1 / ((n : ℝ≥0) + 2))) atTop (𝓝 τ) := by
          rw [← NNReal.tendsto_coe]
          have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
            tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          have h2 : Tendsto (fun n : ℕ => (τ : ℝ) * (1 - ((n : ℝ) + 2)⁻¹)) atTop (𝓝 ((τ : ℝ) * (1 - 0))) :=
            tendsto_const_nhds.mul (tendsto_const_nhds.sub h1)
          rw [sub_zero, mul_one] at h2
          refine h2.congr fun n => ?_
          push_cast
          have hle1 : (1 : ℝ≥0) / ((n : ℝ≥0) + 2) ≤ 1 := by
            rw [div_le_one (by positivity)]; exact le_trans (by norm_num : (1 : ℝ≥0) ≤ 2) (le_add_of_nonneg_left zero_le)
          rw [NNReal.coe_sub hle1]
          simp [one_div]
        exact hCont.continuousAt.tendsto.comp hseq
      refine le_of_tendsto hLim (Filter.Eventually.of_forall fun n => hle_lt _ ?_)
      have hlt1 : 1 - 1 / ((n : ℝ≥0) + 2) < 1 := by
        rw [← NNReal.coe_lt_coe]
        have hle1 : (1 : ℝ≥0) / ((n : ℝ≥0) + 2) ≤ 1 := by
          rw [div_le_one (by positivity)]; exact le_trans (by norm_num : (1 : ℝ≥0) ≤ 2) (le_add_of_nonneg_left zero_le)
        rw [NNReal.coe_sub hle1]
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        simp only [NNReal.coe_one, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast,
          NNReal.coe_ofNat]
        linarith
      calc τ * (1 - 1 / ((n : ℝ≥0) + 2)) < τ * 1 := mul_lt_mul_of_pos_left hlt1 hτ_pos
        _ = τ := mul_one τ
  have hle_all : ∀ u : ℝ≥0, u ≤ τ → X u ω ≤ s := fun u hu => by
    rcases eq_or_lt_of_le hu with rfl | hlt
    · exact hXτ_le
    · exact hle_lt u hlt
  have hXτ_ge : s ≤ X τ ω := by
    have hEx : ∀ n : ℕ, ∃ u : ℝ≥0, 0 < u ∧ s < X u ω ∧ u < τ + 1 / ((n : ℝ≥0) + 1) := fun n => by
      have hlt : sInf ({t : ℝ≥0 | 0 < t ∧ s < X t ω} : Set ℝ≥0) < τ + 1 / ((n : ℝ≥0) + 1) := by
        rw [hτ_eq]; exact lt_add_of_pos_right τ (by positivity)
      obtain ⟨u, ⟨hu1, hu2⟩, hu3⟩ := (csInf_lt_iff (OrderBot.bddBelow _) hex).mp hlt
      exact ⟨u, hu1, hu2, hu3⟩
    choose u hu_pos hu_gt hu_lt using hEx
    have hu_ge : ∀ n : ℕ, τ ≤ u n := fun n => by
      rw [← hτ_eq]; exact csInf_le (OrderBot.bddBelow _) ⟨hu_pos n, hu_gt n⟩
    have hu_lim : Tendsto u atTop (𝓝 τ) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hu_ge (fun n => (hu_lt n).le)
      rw [← NNReal.tendsto_coe]
      have h1 : Tendsto (fun n : ℕ => (τ : ℝ) + ((n : ℝ) + 1)⁻¹) atTop (𝓝 ((τ : ℝ) + 0)) :=
        tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
      rw [add_zero] at h1
      exact h1.congr fun n => by push_cast; simp [one_div]
    exact ge_of_tendsto (hCont.continuousAt.tendsto.comp hu_lim)
      (Filter.Eventually.of_forall fun n => (hu_gt n).le)
  have hXτ : X τ ω = s := le_antisymm hXτ_le hXτ_ge
  refine ⟨hle_all, hXτ, fun h hh => ?_⟩
  let S1 : Set ℝ≥0 := {t : ℝ≥0 | 0 < t ∧ s + h < X t ω}
  let S2 : Set ℝ≥0 := {v : ℝ≥0 | 0 < v ∧ h < X (τ + v) ω - X τ ω}
  have hImg : S1 = (fun v : ℝ≥0 => τ + v) '' S2 := by
    ext t
    simp only [S1, S2, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨ht_pos, hXt⟩
      have hτ_lt : τ < t := by
        by_contra hle
        have := hle_all t (le_of_not_gt hle)
        linarith
      refine ⟨t - τ, ⟨tsub_pos_of_lt hτ_lt, ?_⟩, add_tsub_cancel_of_le hτ_lt.le⟩
      rw [add_tsub_cancel_of_le hτ_lt.le, hXτ]; linarith
    · rintro ⟨v, ⟨hv_pos, hXv⟩, rfl⟩
      refine ⟨lt_of_le_of_lt (zero_le) (lt_add_of_pos_right τ hv_pos), ?_⟩
      rw [hXτ] at hXv; linarith
  dsimp only [Kyprianou.Ch01.firstUpperPassage]
  by_cases hne2 : S2.Nonempty
  · have hne1 : S1.Nonempty := by rw [hImg]; exact hne2.image _
    have hne1' : ∃ t : ℝ≥0, 0 < t ∧ s + h < X t ω := hne1
    have hne2' : ∃ v : ℝ≥0, 0 < v ∧ h < X (τ + v) ω - X τ ω := hne2
    rw [if_pos hne1', if_pos hne2', ← WithTop.coe_add]
    congr 1
    apply le_antisymm
    · change sInf S1 ≤ τ + sInf S2
      rw [hImg]
      have hle_b : ∀ v ∈ S2, sInf ((fun v => τ + v) '' S2) ≤ τ + v := fun v hv =>
        csInf_le (OrderBot.bddBelow _) ⟨v, hv, rfl⟩
      by_contra hgt
      have hlt : τ + sInf S2 < sInf ((fun v => τ + v) '' S2) := lt_of_not_ge hgt
      have hdiff : sInf S2 < sInf ((fun v => τ + v) '' S2) - τ := by
        rw [lt_tsub_iff_left]; exact hlt
      obtain ⟨v, hv, hv_lt⟩ := (csInf_lt_iff (OrderBot.bddBelow _) hne2).mp hdiff
      have h1 := hle_b v hv
      have h2 : τ + v < sInf ((fun v => τ + v) '' S2) := by
        have := lt_tsub_iff_left.mp hv_lt; exact this
      exact not_lt_of_ge h1 h2
    · change τ + sInf S2 ≤ sInf S1
      rw [hImg]
      refine le_csInf (hne2.image _) ?_
      rintro _ ⟨v, hv, rfl⟩
      exact add_le_add le_rfl (csInf_le (OrderBot.bddBelow _) hv)
  · have hno1 : ¬ (∃ t : ℝ≥0, 0 < t ∧ s + h < X t ω) := by
      change ¬ S1.Nonempty; rw [hImg]; simpa using hne2
    have hno2 : ¬ (∃ v : ℝ≥0, 0 < v ∧ h < X (τ + v) ω - X τ ω) := hne2
    rw [if_neg hno1, if_neg hno2, WithTop.add_top]

private lemma indep_naturalSigma_postIncrements
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hL : ProbabilityTheory.IsLevyProcess X P)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (t : ℝ≥0) (d : ℕ) (u : Fin (d + 1) → ℝ≥0) (hu0 : u 0 = 0) (hu_mono : Monotone u) :
    Indep (Kyprianou.Ch01.naturalSigma X t)
      (MeasurableSpace.comap
        (fun ω (j : Fin d) => X (t + u j.succ) ω - X (t + u j.castSucc) ω) inferInstance) P := by
  let Y : Ω → (Fin d → ℝ) := fun ω j => X (t + u j.succ) ω - X (t + u j.castSucc) ω
  have hY_meas : Measurable Y :=
    measurable_pi_lambda _ fun j => (hMeas _).sub (hMeas _)
  let mFin : Finset {r : ℝ≥0 // r ≤ t} → MeasurableSpace Ω :=
    fun S => ⨆ r ∈ S, MeasurableSpace.comap (X r.1) inferInstance
  have hSup_eq : Kyprianou.Ch01.naturalSigma X t = ⨆ S : Finset {r : ℝ≥0 // r ≤ t}, mFin S := by
    apply le_antisymm
    · refine iSup₂_le fun r hr => ?_
      exact le_iSup_of_le ({⟨r, hr⟩} : Finset {r : ℝ≥0 // r ≤ t})
        (le_iSup₂_of_le ⟨r, hr⟩ (Finset.mem_singleton_self _) le_rfl)
    · refine iSup_le fun S => iSup₂_le fun r _ => ?_
      exact le_iSup₂_of_le r.1 r.2 le_rfl
  rw [hSup_eq]
  refine indep_iSup_of_monotone ?_ ?_ hY_meas.comap_le ?_
  · intro S
    let Tfin : Finset ℝ≥0 := (S.image Subtype.val) ∪ {0, t}
    have h0_mem : (0 : ℝ≥0) ∈ Tfin := by simp [Tfin]
    have ht_mem : t ∈ Tfin := by simp [Tfin]
    have hCard_pos : 0 < Tfin.card := Finset.card_pos.mpr ⟨0, h0_mem⟩
    let m : ℕ := Tfin.card - 1
    have hCard : Tfin.card = m + 1 := (Nat.sub_add_cancel hCard_pos).symm
    let rEmb : Fin (m + 1) ↪o ℝ≥0 := Tfin.orderEmbOfFin hCard
    have hr_mem : ∀ k : Fin (m + 1), rEmb k ∈ Tfin := fun k => Finset.orderEmbOfFin_mem Tfin hCard k
    have hr_le_t : ∀ k : Fin (m + 1), rEmb k ≤ t := fun k => by
      have hm := hr_mem k
      simp only [Tfin, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
        Finset.mem_singleton] at hm
      rcases hm with ⟨a, _, ha⟩ | h0 | ht
      · rw [← ha]; exact a.2
      · rw [h0]; exact zero_le
      · rw [ht]
    have hr0 : rEmb 0 = 0 := by
      have hmem0 : (0 : ℝ≥0) ∈ Set.range rEmb := by
        rw [Finset.range_orderEmbOfFin]; exact h0_mem
      obtain ⟨k, hk⟩ := hmem0
      exact le_antisymm (by rw [← hk]; exact rEmb.monotone (Fin.zero_le k)) zero_le
    have hr_last : rEmb (Fin.last m) = t := by
      have hmemt : t ∈ Set.range rEmb := by
        rw [Finset.range_orderEmbOfFin]; exact ht_mem
      obtain ⟨k, hk⟩ := hmemt
      exact le_antisymm (hr_le_t (Fin.last m)) (by rw [← hk]; exact rEmb.monotone (Fin.le_last k))
    let g : Fin (m + d + 1) → ℝ≥0 := fun i =>
      if hi : i.1 ≤ m then rEmb ⟨i.1, Nat.lt_succ_of_le hi⟩
      else t + u ⟨i.1 - m, by omega⟩
    have hg_mono : Monotone g := by
      intro i j hij
      dsimp only [g]
      split_ifs with hi hj hj
      · exact rEmb.monotone (by exact hij)
      · exact le_trans (hr_le_t _) (le_self_add)
      · omega
      · exact add_le_add le_rfl (hu_mono (Fin.mk_le_mk.mpr (by omega)))
    have hInd := hL.indep_increments (m + d) g hg_mono
    let Δ : Fin (m + d) → Ω → ℝ := fun k => ProbabilityTheory.increment X (g k.castSucc) (g k.succ)
    have hΔ_meas : ∀ k, Measurable (Δ k) := fun k => (hMeas _).sub (hMeas _)
    let S1 : Set (Fin (m + d)) := {k | k.1 < m}
    let S2 : Set (Fin (m + d)) := {k | m ≤ k.1}
    have hDisj : Disjoint S1 S2 := Set.disjoint_left.mpr fun k h1 h2 => not_lt_of_ge (show m ≤ k.1 from h2) (show k.1 < m from h1)
    have hInd_disj : Indep (⨆ k ∈ S1, MeasurableSpace.comap (Δ k) inferInstance)
        (⨆ k ∈ S2, MeasurableSpace.comap (Δ k) inferInstance) P :=
      indep_iSup_of_disjoint (fun k => (hΔ_meas k).comap_le) hInd hDisj
    have hInd_mono : ∀ {m1 m2 m1' m2' : MeasurableSpace Ω}, m1 ≤ m1' → m2 ≤ m2' → Indep m1' m2' P → Indep m1 m2 P :=
      fun h1 h2 h => indep_of_indep_of_le_left (indep_of_indep_of_le_right h h2) h1
    refine hInd_mono ?_ ?_ hInd_disj
    · refine iSup₂_le fun a ha => ?_
      have ha_mem : a.1 ∈ Set.range rEmb := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
      obtain ⟨k, hk⟩ := ha_mem
      have hX_sum : X a.1 = fun ω => ∑ i : Fin k.1, Δ ⟨i.1, by omega⟩ ω := by
        ext ω
        rw [← hk]
        have hTel : ∀ j : ℕ, (hj : j ≤ m) →
            X (rEmb ⟨j, Nat.lt_succ_of_le hj⟩) ω = ∑ i : Fin j, Δ ⟨i.1, by omega⟩ ω := by
          intro j
          induction j with
          | zero =>
              intro _
              have h0x : X 0 ω = 0 := congrFun hL.start_zero ω
              simp [hr0, h0x]
          | succ j ih =>
              intro hj
              rw [Fin.sum_univ_castSucc]; simp only [Fin.coe_castSucc, Fin.val_last]; rw [← ih (Nat.le_of_succ_le hj)]
              have hΔj : Δ ⟨j, by omega⟩ ω =
                  X (rEmb ⟨j + 1, Nat.lt_succ_of_le hj⟩) ω -
                    X (rEmb ⟨j, Nat.lt_succ_of_le (Nat.le_of_succ_le hj)⟩) ω := by
                dsimp only [Δ, ProbabilityTheory.increment, g]
                simp [Nat.le_of_succ_le hj, hj]
              linarith
        exact hTel k.1 (Nat.lt_succ_iff.mp k.2)
      rw [hX_sum]
      letI : MeasurableSpace Ω := ⨆ i ∈ S1, MeasurableSpace.comap (Δ i) inferInstance
      have hmeas_sum : Measurable (fun ω => ∑ i : Fin k.1, Δ ⟨i.1, by omega⟩ ω) := by
        refine Finset.measurable_sum _ fun i _ => ?_
        have hle : MeasurableSpace.comap (Δ ⟨i.1, by omega⟩) inferInstance ≤
            ⨆ idx ∈ S1, MeasurableSpace.comap (Δ idx) inferInstance :=
          le_iSup₂_of_le (⟨i.1, by omega⟩ : Fin (m + d)) (show i.1 < m by omega) le_rfl
        exact Measurable.mono (comap_measurable _) hle le_rfl
      exact hmeas_sum.comap_le
    · letI : MeasurableSpace Ω := ⨆ i ∈ S2, MeasurableSpace.comap (Δ i) inferInstance
      have hmeas_Y : Measurable Y := by
        refine measurable_pi_lambda _ fun j => ?_
        have hEq_j : (fun ω => Y ω j) = Δ ⟨m + j.1, by omega⟩ := by
          ext ω
          dsimp only [Y, Δ, ProbabilityTheory.increment, g]
          have h1 : ¬ (m + j.1 + 1 ≤ m) := by omega
          have hsub1 : m + j.1 + 1 - m = j.1 + 1 := by omega
          by_cases hj0 : j.1 = 0
          · have hle_m : m + j.1 ≤ m := by omega
            have hj_eq0 : j.castSucc = 0 := Fin.ext hj0
            simp only [Fin.val_succ, Fin.val_castSucc]
            rw [dif_neg h1, dif_pos hle_m]
            have hrm : (⟨m + j.1, Nat.lt_succ_of_le hle_m⟩ : Fin (m + 1)) = Fin.last m :=
              Fin.ext (by simp [Fin.last, hj0])
            have hjs : (⟨m + j.1 + 1 - m, by omega⟩ : Fin (d + 1)) = j.succ :=
              Fin.ext (by simp [Fin.succ, hsub1])
            rw [hrm, hr_last, hj_eq0, hu0, add_zero, hjs]
          · have h2 : ¬ (m + j.1 ≤ m) := by omega
            have hsub2 : m + j.1 - m = j.1 := by omega
            simp only [Fin.val_succ, Fin.val_castSucc]
            rw [dif_neg h1, dif_neg h2]
            have hjs : (⟨m + j.1 + 1 - m, by omega⟩ : Fin (d + 1)) = j.succ :=
              Fin.ext (by simp [Fin.succ, hsub1])
            have hjc : (⟨m + j.1 - m, by omega⟩ : Fin (d + 1)) = j.castSucc :=
              Fin.ext (by simp [Fin.castSucc, hsub2])
            rw [hjs, hjc]
        rw [hEq_j]
        have hle : MeasurableSpace.comap (Δ ⟨m + j.1, by omega⟩) inferInstance ≤
            ⨆ idx ∈ S2, MeasurableSpace.comap (Δ idx) inferInstance :=
          le_iSup₂_of_le (⟨m + j.1, by omega⟩ : Fin (m + d)) (show m ≤ m + j.1 by omega) le_rfl
        exact Measurable.mono (comap_measurable _) hle le_rfl
      exact hmeas_Y.comap_le
  · intro S
    exact iSup₂_le fun r _ => (hMeas r.1).comap_le
  · intro S1 S2 h12
    exact iSup₂_le fun r hr => le_iSup₂_of_le r (h12 hr) le_rfl

private lemma integral_exp_postIncrements_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hL : ProbabilityTheory.IsLevyProcess X P)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (t : ℝ≥0) (d : ℕ) (u : Fin (d + 1) → ℝ≥0) (hu0 : u 0 = 0) (hu_mono : Monotone u)
    (ξ : Fin d → ℝ)
    (B : Set Ω) (hB : @MeasurableSet Ω (Kyprianou.Ch01.naturalSigma X t) B) :
    (∫ ω in B,
      Complex.exp (Complex.I *
        ((∑ j : Fin d, ξ j * (X (t + u j.succ) ω - X (t + u j.castSucc) ω) : ℝ) : ℂ)) ∂P) =
      ((P B).toReal : ℂ) *
        (∫ ω,
          Complex.exp (Complex.I *
            ((∑ j : Fin d, ξ j * (X (u j.succ) ω - X (u j.castSucc) ω) : ℝ) : ℂ)) ∂P) := by
  let Y : Ω → (Fin d → ℝ) := fun ω j => X (t + u j.succ) ω - X (t + u j.castSucc) ω
  let ψ : (Fin d → ℝ) → ℂ := fun v => Complex.exp (Complex.I * ((∑ j : Fin d, ξ j * v j : ℝ) : ℂ))
  have hψ_cont : Continuous ψ := by
    dsimp only [ψ]
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j))))
  have hB_meas : MeasurableSet B := by
    have hle : Kyprianou.Ch01.naturalSigma X t ≤ ‹MeasurableSpace Ω› :=
      iSup₂_le fun r _ => (hMeas r).comap_le
    exact hle B hB
  have hInd_m := indep_naturalSigma_postIncrements P X hL hMeas t d u hu0 hu_mono
  have hIndFun : IndepFun (B.indicator (fun _ : Ω => (1 : ℂ))) (ψ ∘ Y) P := by
    rw [IndepFun_iff_Indep]
    have hInd_mono : ∀ {m1 m2 m1' m2' : MeasurableSpace Ω}, m1 ≤ m1' → m2 ≤ m2' → Indep m1' m2' P → Indep m1 m2 P :=
      fun h1 h2 h => indep_of_indep_of_le_left (indep_of_indep_of_le_right h h2) h1
    refine hInd_mono ?_ ?_ hInd_m
    · letI : MeasurableSpace Ω := Kyprianou.Ch01.naturalSigma X t
      exact (measurable_const.indicator hB).comap_le
    · letI : MeasurableSpace Ω := MeasurableSpace.comap Y inferInstance
      exact (hψ_cont.measurable.comp (comap_measurable Y)).comap_le
  have hY_meas : Measurable Y := measurable_pi_lambda _ fun j => (hMeas _).sub (hMeas _)
  have hInt_B : (∫ ω in B, (ψ ∘ Y) ω ∂P) = ((P B).toReal : ℂ) * (∫ ω, (ψ ∘ Y) ω ∂P) := by
    have h1 : (∫ ω in B, (ψ ∘ Y) ω ∂P) =
        ∫ ω, B.indicator (fun _ : Ω => (1 : ℂ)) ω * (ψ ∘ Y) ω ∂P := by
      rw [← integral_indicator hB_meas]
      congr 1; ext ω; by_cases hω : ω ∈ B <;> simp [hω]
    rw [h1, hIndFun.integral_fun_mul_eq_mul_integral
      (measurable_const.indicator hB_meas).aestronglyMeasurable
      (hψ_cont.measurable.comp hY_meas).aestronglyMeasurable,
      integral_indicator hB_meas, setIntegral_const, Complex.real_smul, mul_one, Measure.real]
  change (∫ ω in B, (ψ ∘ Y) ω ∂P) = _
  rw [hInt_B]
  congr 1
  -- Show ∫ (ψ ∘ Y) = ∫ (ψ ∘ Y_0) via factorization of independent increments + stationarity
  have hFactor : ∀ s : ℝ≥0,
      (∫ ω, Complex.exp (Complex.I *
        ((∑ j : Fin d, ξ j * (X (s + u j.succ) ω - X (s + u j.castSucc) ω) : ℝ) : ℂ)) ∂P) =
      ∏ j : Fin d,
        ∫ ω, Complex.exp (Complex.I *
          ((ξ j * (X (s + u j.succ) ω - X (s + u j.castSucc) ω) : ℝ) : ℂ)) ∂P := by
    intro s
    have hInd_s : iIndepFun (fun j : Fin d =>
        ProbabilityTheory.increment X (s + u j.castSucc) (s + u j.succ)) P :=
      hL.indep_increments d (fun i => s + u i) (fun _ _ h => add_le_add le_rfl (hu_mono h))
    let f : Fin d → Ω → ℂ := fun j ω =>
      Complex.exp (Complex.I * ((ξ j * (X (s + u j.succ) ω - X (s + u j.castSucc) ω) : ℝ) : ℂ))
    have hf_meas : ∀ j, Measurable (f j) := fun j =>
      Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (measurable_const.mul ((hMeas _).sub (hMeas _)))))
    have hf_ind : iIndepFun f P :=
      hInd_s.comp (fun j x => Complex.exp (Complex.I * ((ξ j * x : ℝ) : ℂ)))
        (fun j => Complex.continuous_exp.measurable.comp
          (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
            (measurable_const.mul measurable_id))))
    have hProd_eq : (fun ω => Complex.exp (Complex.I *
        ((∑ j : Fin d, ξ j * (X (s + u j.succ) ω - X (s + u j.castSucc) ω) : ℝ) : ℂ))) =
        fun ω => ∏ j ∈ Finset.univ, f j ω := by
      ext ω
      dsimp only [f]
      rw [← Complex.exp_sum, Complex.ofReal_sum, Finset.mul_sum]
    rw [hProd_eq]
    have hGen : ∀ S : Finset (Fin d),
        (∫ ω, ∏ j ∈ S, f j ω ∂P) = ∏ j ∈ S, ∫ ω, f j ω ∂P := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | @insert j S hj ih =>
          simp_rw [Finset.prod_insert hj]
          have hind_j : IndepFun (f j) (fun ω => ∏ i ∈ S, f i ω) P := by
            have h1 := (hf_ind.indepFun_finsetProd_of_notMem hf_meas hj).symm
            have hEqp : (∏ i ∈ S, f i) = fun ω => ∏ i ∈ S, f i ω := by ext ω; simp
            rwa [hEqp] at h1
          rw [hind_j.integral_fun_mul_eq_mul_integral (hf_meas j).aestronglyMeasurable
            (Finset.measurable_prod S fun i _ => hf_meas i).aestronglyMeasurable, ih]
    exact hGen Finset.univ
  have hY0 : (fun ω => Complex.exp (Complex.I *
      ((∑ j : Fin d, ξ j * (X (u j.succ) ω - X (u j.castSucc) ω) : ℝ) : ℂ))) =
      fun ω => Complex.exp (Complex.I *
        ((∑ j : Fin d, ξ j * (X (0 + u j.succ) ω - X (0 + u j.castSucc) ω) : ℝ) : ℂ)) := by
    ext ω; simp
  change (∫ ω, Complex.exp (Complex.I *
      ((∑ j : Fin d, ξ j * (X (t + u j.succ) ω - X (t + u j.castSucc) ω) : ℝ) : ℂ)) ∂P) = _
  rw [hY0, hFactor t, hFactor 0]
  refine Finset.prod_congr rfl fun j _ => ?_
  let δ : ℝ≥0 := u j.succ - u j.castSucc
  have hle : u j.castSucc ≤ u j.succ := hu_mono (Fin.castSucc_le_succ j)
  have ht_eq : t + u j.succ = (t + u j.castSucc) + δ := by
    rw [add_assoc, add_tsub_cancel_of_le hle]
  have h0_eq : 0 + u j.succ = (0 + u j.castSucc) + δ := by
    rw [add_assoc, add_tsub_cancel_of_le hle]
  have hid1 := hL.stationary_increments (t + u j.castSucc) δ
  have hid2 := hL.stationary_increments (0 + u j.castSucc) δ
  have hid : IdentDistrib
      (ProbabilityTheory.increment X (t + u j.castSucc) (t + u j.succ))
      (ProbabilityTheory.increment X (0 + u j.castSucc) (0 + u j.succ)) P P := by
    rw [ht_eq, h0_eq]; exact hid1.trans hid2.symm
  have hcomp := hid.comp (u := fun x : ℝ => Complex.exp (Complex.I * ((ξ j * x : ℝ) : ℂ)))
    (Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        (measurable_const.mul measurable_id))))
  exact hcomp.integral_eq

private lemma strongMarkov_firstUpperPassage_lt
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hL : ProbabilityTheory.IsLevyProcess X P)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hCont : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ≥0) (hs : 0 < s)
    (hFin_s : ∀ᵐ ω ∂P, Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω ≠ ⊤)
    (A : Set Ω) (hA_meas : MeasurableSet A)
    (hA_stop : ∀ t : ℝ≥0, @MeasurableSet Ω (Kyprianou.Ch01.naturalSigma X t)
      (A ∩ {ω | Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω < (t : WithTop ℝ≥0)})) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun u ω =>
        if u = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage X (u : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    ∀ (h : ℝ≥0) (hh : 0 < h),
      (∀ᵐ ω ∂P, Kyprianou.Ch01.firstUpperPassage X ((s + h : ℝ≥0) : ℝ) ω ≠ ⊤) →
      (∀ᵐ ω ∂P, Kyprianou.Ch01.firstUpperPassage X (h : ℝ) ω ≠ ⊤) →
      ∀ (a : ℝ),
        P (A ∩ {ω | T (s + h) ω - T s ω < a}) = P A * P {ω | T h ω < a} := by
  intro T h hh hFin_sh hFin_h a
  have hX0_all : ∀ ω, X 0 ω = 0 := fun ω => congrFun hL.start_zero ω
  let τR : Ω → ℝ≥0 := fun ω =>
    match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
    | none => 0
    | some t => t
  have hτR_meas : Measurable τR := by
    have hT_meas := Kyprianou.Ch01.zeroBoundaryPassageClockMeasurableV1 X hMeas hCont s
    have hEq : (fun ω => (τR ω : ℝ)) =
        fun ω => if s = 0 then (0 : ℝ) else
          match Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
          | none => (0 : ℝ)
          | some t => (t : ℝ) := by
      ext ω; dsimp only [τR]; rw [if_neg hs.ne']; cases Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω <;> rfl
    have hEq' : τR = fun ω => Real.toNNReal ((τR ω : ℝ)) := funext fun ω => (Real.toNNReal_coe).symm
    rw [hEq']
    exact measurable_real_toNNReal.comp (hEq ▸ hT_meas)
  let Xtilde : ℝ≥0 → Ω → ℝ := fun u ω => X (τR ω + u) ω - X (τR ω) ω
  have hXtilde_cont : ∀ ω, Continuous (fun u : ℝ≥0 => Xtilde u ω) := fun ω =>
    ((hCont ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hXtilde_meas : ∀ u : ℝ≥0, Measurable (Xtilde u) := by
    intro u
    have hMeas_eval : ∀ g : Ω → ℝ≥0, Measurable g → Measurable (fun ω => X (g ω) ω) := by
      intro g hg
      let gN : ℕ → Ω → ℝ≥0 := fun N ω =>
        ((Nat.floor ((g ω : ℝ) * (2 : ℝ) ^ N) : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ N)
      have hMeas_gN : ∀ N : ℕ, Measurable (fun ω => X (gN N ω) ω) := by
        intro N
        have hFloor_meas : Measurable (fun ω => Nat.floor ((g ω : ℝ) * (2 : ℝ) ^ N)) :=
          Nat.measurable_floor.comp ((NNReal.continuous_coe.measurable.comp hg).mul measurable_const)
        refine measurable_of_isOpen fun U hU => ?_
        have hPre : (fun ω => X (gN N ω) ω) ⁻¹' U =
            ⋃ k : ℕ, ({ω | Nat.floor ((g ω : ℝ) * (2 : ℝ) ^ N) = k} ∩
              (X ((k : ℝ≥0) / (2 : ℝ≥0) ^ N)) ⁻¹' U) := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · intro hmem; exact ⟨Nat.floor ((g ω : ℝ) * (2 : ℝ) ^ N), rfl, hmem⟩
          · rintro ⟨k, hk, hmem⟩; dsimp only [gN]; rw [hk]; exact hmem
        rw [hPre]
        exact MeasurableSet.iUnion fun k =>
          (hFloor_meas (measurableSet_singleton k)).inter (hMeas _ hU.measurableSet)
      refine measurable_of_tendsto_metrizable hMeas_gN (tendsto_pi_nhds.mpr fun ω => ?_)
      have hg_lim : Tendsto (fun N => gN N ω) atTop (𝓝 (g ω)) := by
        rw [← NNReal.tendsto_coe]
        have hle : ∀ N : ℕ, ((gN N ω : ℝ≥0) : ℝ) ≤ (g ω : ℝ) := fun N => by
          dsimp only [gN]; push_cast
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ N)]
          exact Nat.floor_le (mul_nonneg (g ω).2 (by positivity))
        have hge : ∀ N : ℕ, (g ω : ℝ) - 1 / (2 : ℝ) ^ N ≤ ((gN N ω : ℝ≥0) : ℝ) := fun N => by
          dsimp only [gN]; push_cast
          have h1 : (g ω : ℝ) * (2 : ℝ) ^ N - 1 < (Nat.floor ((g ω : ℝ) * (2 : ℝ) ^ N) : ℝ) := by
            have := Nat.lt_floor_add_one ((g ω : ℝ) * (2 : ℝ) ^ N); linarith
          have h2p : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
          rw [sub_le_iff_le_add]
          have h3 : (g ω : ℝ) * (2 : ℝ) ^ N ≤ (Nat.floor ((g ω : ℝ) * (2 : ℝ) ^ N) : ℝ) + 1 := by linarith
          have h4 : (g ω : ℝ) ≤ ((Nat.floor ((g ω : ℝ) * (2 : ℝ) ^ N) : ℝ) + 1) / (2 : ℝ) ^ N :=
            (le_div_iff₀ h2p).mpr h3
          rw [add_div] at h4
          linarith
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hge hle
        have hpow : Tendsto (fun N : ℕ => (1 / (2 : ℝ)) ^ N) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
        have hlim := tendsto_const_nhds (x := (g ω : ℝ)).sub hpow
        rw [sub_zero] at hlim
        exact hlim.congr fun N => by simp [one_div, inv_pow]
      exact (hCont ω).continuousAt.tendsto.comp hg_lim
    exact (hMeas_eval (fun ω => τR ω + u) (hτR_meas.add measurable_const)).sub
      (hMeas_eval τR hτR_meas)
  -- Step 1: Finite-dimensional Strong Markov identity for increments of Xtilde on A
  have hFD_law : ∀ (d : ℕ) (u : Fin (d + 1) → ℝ≥0), u 0 = 0 → Monotone u →
      (P.restrict A).map (fun ω => WithLp.toLp 2 (fun j : Fin d => Xtilde (u j.succ) ω - Xtilde (u j.castSucc) ω)) =
      P A • P.map (fun ω => WithLp.toLp 2 (fun j : Fin d => X (u j.succ) ω - X (u j.castSucc) ω)) := by
    intro d u hu0 hu_mono
    let Δt : Ω → EuclideanSpace ℝ (Fin d) :=
      fun ω => WithLp.toLp 2 (fun j : Fin d => Xtilde (u j.succ) ω - Xtilde (u j.castSucc) ω)
    let Δ0 : Ω → EuclideanSpace ℝ (Fin d) :=
      fun ω => WithLp.toLp 2 (fun j : Fin d => X (u j.succ) ω - X (u j.castSucc) ω)
    have hΔt_meas : Measurable Δt :=
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp
        (measurable_pi_lambda _ fun j => (hXtilde_meas _).sub (hXtilde_meas _))
    have hΔ0_meas : Measurable Δ0 :=
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp
        (measurable_pi_lambda _ fun j => (hMeas _).sub (hMeas _))
    haveI : IsFiniteMeasure ((P.restrict A).map Δt) := by
      refine ⟨?_⟩
      rw [Measure.map_apply hΔt_meas MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]
      exact measure_lt_top P A
    haveI : IsFiniteMeasure (P A • P.map Δ0) := by
      refine ⟨?_⟩
      rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hΔ0_meas MeasurableSet.univ,
        Set.preimage_univ, measure_univ, mul_one]
      exact measure_lt_top P A
    refine Measure.ext_of_charFun (funext fun ξ => ?_)
    rw [charFun_apply, charFun_apply,
      integral_map hΔt_meas.aemeasurable (by fun_prop),
      integral_smul_measure,
      integral_map hΔ0_meas.aemeasurable (by fun_prop)]
    have hInner : ∀ v : Fin d → ℝ,
        ((inner ℝ (WithLp.toLp 2 v) ξ : ℝ) : ℂ) * Complex.I =
          Complex.I * ((∑ j : Fin d, ξ j * v j : ℝ) : ℂ) := fun v => by
      rw [EuclideanSpace.inner_eq_star_dotProduct, mul_comm]
      simp [dotProduct, mul_comm]
    simp_rw [Δt, Δ0, hInner]
    change (∫ ω in A, Complex.exp (Complex.I *
        ((∑ j : Fin d, ξ j * (Xtilde (u j.succ) ω - Xtilde (u j.castSucc) ω) : ℝ) : ℂ)) ∂P) =
      (P A).toReal • (∫ ω, Complex.exp (Complex.I *
        ((∑ j : Fin d, ξ j * (X (u j.succ) ω - X (u j.castSucc) ω) : ℝ) : ℂ)) ∂P)
    rw [Complex.real_smul]
    let τN : ℕ → Ω → ℝ≥0 := fun N ω =>
      (((Nat.floor ((τR ω : ℝ) * (2 : ℝ) ^ N) + 1 : ℕ) : ℝ≥0)) / ((2 : ℝ≥0) ^ N)
    let Φ : ℝ≥0 → Ω → ℂ := fun t ω =>
      Complex.exp (Complex.I *
        ((∑ j : Fin d, ξ j * (X (t + u j.succ) ω - X (t + u j.castSucc) ω) : ℝ) : ℂ))
    have hΦ_eq_tilde : ∀ ω,
        Complex.exp (Complex.I *
          ((∑ j : Fin d, ξ j * (Xtilde (u j.succ) ω - Xtilde (u j.castSucc) ω) : ℝ) : ℂ)) =
        Φ (τR ω) ω := fun ω => by
      dsimp only [Φ, Xtilde]
      congr 3; refine Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hΦ_eq_tilde]
    have hStepN : ∀ N : ℕ,
        (∫ ω in A, Φ (τN N ω) ω ∂P) =
        ((P A).toReal : ℂ) * (∫ ω, Φ 0 ω ∂P) := by
      intro N
      let tNk : ℕ → ℝ≥0 := fun k => (((k + 1 : ℕ) : ℝ≥0)) / ((2 : ℝ≥0) ^ N)
      let EN : ℕ → Set Ω := fun k =>
        A ∩ ({ω | Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω < (tNk k : WithTop ℝ≥0)} \
          {ω | Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω < (((k : ℝ≥0) / (2 : ℝ≥0) ^ N) : WithTop ℝ≥0)})
      have hEN_nat : ∀ k : ℕ, @MeasurableSet Ω (Kyprianou.Ch01.naturalSigma X (tNk k)) (EN k) := fun k => by
        have hEq : EN k =
            (A ∩ {ω | Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω < (tNk k : WithTop ℝ≥0)}) \
              (A ∩ {ω | Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω < (((k : ℝ≥0) / (2 : ℝ≥0) ^ N) : WithTop ℝ≥0)}) := by
          ext ω; simp [EN]; tauto
        rw [hEq]
        letI : MeasurableSpace Ω := Kyprianou.Ch01.naturalSigma X (tNk k)
        have hle_k : Kyprianou.Ch01.naturalSigma X ((k : ℝ≥0) / (2 : ℝ≥0) ^ N) ≤
            Kyprianou.Ch01.naturalSigma X (tNk k) := by
          refine iSup₂_le fun r hr => le_iSup₂_of_le r (le_trans hr ?_) le_rfl
          dsimp only [tNk]
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (zero_le)
        exact (hA_stop (tNk k)).diff (hle_k _ (hA_stop _))
      have hEN_meas : ∀ k : ℕ, MeasurableSet (EN k) := fun k =>
        (iSup₂_le fun r _ => (hMeas r).comap_le) _ (hEN_nat k)
      have hEN_disj : Pairwise (Function.onFun Disjoint EN) := by
        intro j k hjk
        refine Set.disjoint_left.mpr fun ω hj hk => ?_
        rcases lt_or_gt_of_ne hjk with hlt | hgt
        · have hle : tNk j ≤ (k : ℝ≥0) / (2 : ℝ≥0) ^ N := by
            dsimp only [tNk]
            exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) (zero_le)
          exact hk.2.2 (lt_of_lt_of_le hj.2.1 (WithTop.coe_le_coe.mpr hle))
        · have hle : tNk k ≤ (j : ℝ≥0) / (2 : ℝ≥0) ^ N := by
            dsimp only [tNk]
            exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hgt) (zero_le)
          exact hj.2.2 (lt_of_lt_of_le hk.2.1 (WithTop.coe_le_coe.mpr hle))
      have hUnion_ae : (⋃ k : ℕ, EN k) =ᵐ[P] A := by
        filter_upwards [hFin_s] with ω hfin
        change (ω ∈ ⋃ k : ℕ, EN k) = (ω ∈ A)
        apply propext
        constructor
        · rintro ⟨_, ⟨k, rfl⟩, hk⟩; exact hk.1
        · intro hωA
          cases hval : Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
          | top => exact absurd hval hfin
          | coe τ =>
              refine Set.mem_iUnion.mpr ⟨Nat.floor ((τ : ℝ) * (2 : ℝ) ^ N), hωA, ?_, ?_⟩
              · change Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω < (tNk _ : WithTop ℝ≥0)
                rw [hval, WithTop.coe_lt_coe, ← NNReal.coe_lt_coe]
                dsimp only [tNk]; push_cast
                rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)]
                exact Nat.lt_floor_add_one _
              · change ¬ (Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω < _)
                rw [hval, not_lt, WithTop.coe_le_coe, ← NNReal.coe_le_coe]
                push_cast
                rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)]
                exact Nat.floor_le (mul_nonneg τ.2 (by positivity))
      have hτN_on : ∀ k : ℕ, ∀ ω ∈ EN k, τN N ω = tNk k := by
        intro k ω hω
        have hfin : Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω ≠ ⊤ := by
          intro htop
          have h1 : Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω < (tNk k : WithTop ℝ≥0) := hω.2.1
          rw [htop] at h1; exact not_top_lt h1
        cases hval : Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
        | top => exact absurd hval hfin
        | coe τ =>
            have hτ_eq : τR ω = τ := by dsimp only [τR]; rw [hval]
            have hlt : τ < tNk k := by
              have h1 : Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω < (tNk k : WithTop ℝ≥0) := hω.2.1
              rw [hval] at h1; exact WithTop.coe_lt_coe.mp h1
            have hge : (k : ℝ≥0) / (2 : ℝ≥0) ^ N ≤ τ := by
              have h1 : ¬ (Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω < (((k : ℝ≥0) / (2 : ℝ≥0) ^ N) : WithTop ℝ≥0)) := hω.2.2
              rw [hval] at h1; exact WithTop.coe_le_coe.mp (le_of_not_gt h1)
            have hfl : Nat.floor ((τ : ℝ) * (2 : ℝ) ^ N) = k := by
              rw [Nat.floor_eq_iff (a := (τ : ℝ) * (2 : ℝ) ^ N) (by positivity)]
              constructor
              · have h1 : (((k : ℝ≥0) / (2 : ℝ≥0) ^ N : ℝ≥0) : ℝ) ≤ (τ : ℝ) := NNReal.coe_le_coe.mpr hge
                push_cast at h1; exact (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)).mp h1
              · have h2 : (τ : ℝ) < ((tNk k : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.mpr hlt
                dsimp only [tNk] at h2; push_cast at h2
                exact (lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)).mp h2
            dsimp only [τN, tNk]; rw [hτ_eq, hfl]
      have hInt_ΦN : IntegrableOn (fun ω => Φ (τN N ω) ω) (⋃ k, EN k) P := by
        refine (integrableOn_const (C := (1 : ℝ)) (hs := measure_ne_top P _)).mono' ?_ ?_
        · have hMeas_piece : ∀ k, Measurable (fun ω => Φ (tNk k) ω) := fun k =>
            Complex.continuous_exp.measurable.comp
              (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
                (Finset.measurable_sum _ fun j _ => measurable_const.mul ((hMeas _).sub (hMeas _)))))
          have hMeas_τN : Measurable (fun ω => Φ (τN N ω) ω) := by
            have hFl_meas : Measurable (fun ω => Nat.floor ((τR ω : ℝ) * (2 : ℝ) ^ N)) :=
              Nat.measurable_floor.comp ((NNReal.continuous_coe.measurable.comp hτR_meas).mul measurable_const)
            refine measurable_of_isOpen fun U hU => ?_
            have hPre : (fun ω => Φ (τN N ω) ω) ⁻¹' U =
                ⋃ k : ℕ, ({ω | Nat.floor ((τR ω : ℝ) * (2 : ℝ) ^ N) = k} ∩ (fun ω => Φ (tNk k) ω) ⁻¹' U) := by
              ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
              constructor
              · intro hm; exact ⟨Nat.floor ((τR ω : ℝ) * (2 : ℝ) ^ N), rfl, hm⟩
              · rintro ⟨k, hk, hm⟩; dsimp only [τN, tNk] at hm ⊢; rw [hk]; exact hm
            rw [hPre]
            exact MeasurableSet.iUnion fun k =>
              (hFl_meas (measurableSet_singleton k)).inter (hMeas_piece k hU.measurableSet)
          exact hMeas_τN.aestronglyMeasurable
        · exact Filter.Eventually.of_forall fun ω => by
            dsimp only [Φ]; rw [Complex.norm_exp_I_mul_ofReal]
      rw [← setIntegral_congr_set hUnion_ae,
        integral_iUnion hEN_meas hEN_disj hInt_ΦN]
      have hTerm : ∀ k : ℕ,
          (∫ ω in EN k, Φ (τN N ω) ω ∂P) = ((P (EN k)).toReal : ℂ) * (∫ ω, Φ 0 ω ∂P) := fun k => by
        rw [setIntegral_congr_fun (hEN_meas k) fun ω hω => by rw [hτN_on k ω hω]]
        simpa [Φ] using integral_exp_postIncrements_eq P X hL hMeas (tNk k) d u hu0 hu_mono ξ (EN k) (hEN_nat k)
      simp_rw [hTerm]
      rw [tsum_mul_right]
      congr 1
      have hSumP : ∑' k : ℕ, (P (EN k)).toReal = (P A).toReal := by
        rw [← measure_congr hUnion_ae, measure_iUnion hEN_disj hEN_meas,
          ENNReal.tsum_toReal_eq (fun k => measure_ne_top P _)]
      rw [← Complex.ofReal_tsum, hSumP]
    have hDCT : Tendsto (fun N : ℕ => ∫ ω in A, Φ (τN N ω) ω ∂P) atTop
        (𝓝 (∫ ω in A, Φ (τR ω) ω ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
        (integrableOn_const (hs := measure_ne_top P _)) ?_ ?_
      · intro N
        have hFl_meas : Measurable (fun ω => Nat.floor ((τR ω : ℝ) * (2 : ℝ) ^ N)) :=
          Nat.measurable_floor.comp ((NNReal.continuous_coe.measurable.comp hτR_meas).mul measurable_const)
        have hMeas_piece : ∀ k : ℕ, Measurable (fun ω => Φ ((((k + 1 : ℕ) : ℝ≥0)) / ((2 : ℝ≥0) ^ N)) ω) :=
          fun k => Complex.continuous_exp.measurable.comp
            (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
              (Finset.measurable_sum _ fun j _ => measurable_const.mul ((hMeas _).sub (hMeas _)))))
        refine (measurable_of_isOpen fun U hU => ?_).aestronglyMeasurable
        have hPre : (fun ω => Φ (τN N ω) ω) ⁻¹' U =
            ⋃ k : ℕ, ({ω | Nat.floor ((τR ω : ℝ) * (2 : ℝ) ^ N) = k} ∩
              (fun ω => Φ ((((k + 1 : ℕ) : ℝ≥0)) / ((2 : ℝ≥0) ^ N)) ω) ⁻¹' U) := by
          ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · intro hm; exact ⟨Nat.floor ((τR ω : ℝ) * (2 : ℝ) ^ N), rfl, hm⟩
          · rintro ⟨k, hk, hm⟩; dsimp only [τN] at hm ⊢; rw [hk]; exact hm
        rw [hPre]
        exact MeasurableSet.iUnion fun k =>
          (hFl_meas (measurableSet_singleton k)).inter (hMeas_piece k hU.measurableSet)
      · intro N
        exact Filter.Eventually.of_forall fun ω => by
          dsimp only [Φ]; rw [Complex.norm_exp_I_mul_ofReal]
      · refine Filter.Eventually.of_forall fun ω => ?_
        have hτN_lim : Tendsto (fun N : ℕ => τN N ω) atTop (𝓝 (τR ω)) := by
          rw [← NNReal.tendsto_coe]
          have hge : ∀ N : ℕ, (τR ω : ℝ) ≤ ((τN N ω : ℝ≥0) : ℝ) := fun N => by
            dsimp only [τN]; push_cast
            rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)]
            exact (Nat.lt_floor_add_one _).le
          have hle : ∀ N : ℕ, ((τN N ω : ℝ≥0) : ℝ) ≤ (τR ω : ℝ) + 1 / (2 : ℝ) ^ N := fun N => by
            dsimp only [τN]; push_cast
            have h2p : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
            rw [add_div]
            have h1 : (Nat.floor ((τR ω : ℝ) * (2 : ℝ) ^ N) : ℝ) / (2 : ℝ) ^ N ≤ (τR ω : ℝ) :=
              (div_le_iff₀ h2p).mpr (Nat.floor_le (mul_nonneg (τR ω).2 h2p.le))
            linarith
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hge hle
          have hpow : Tendsto (fun N : ℕ => (1 / (2 : ℝ)) ^ N) atTop (𝓝 0) :=
            tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
          have hlim := tendsto_const_nhds (x := (τR ω : ℝ)).add hpow
          rw [add_zero] at hlim
          exact hlim.congr fun N => by simp [one_div, inv_pow]
        have hΦ_cont : Continuous (fun t : ℝ≥0 => Φ t ω) := by
          dsimp only [Φ]
          exact Complex.continuous_exp.comp
            (continuous_const.mul (Complex.continuous_ofReal.comp
              (continuous_finset_sum _ fun j _ => continuous_const.mul
                (((hCont ω).comp (continuous_id.add continuous_const)).sub
                  ((hCont ω).comp (continuous_id.add continuous_const))))))
        exact hΦ_cont.continuousAt.tendsto.comp hτN_lim
    have hConst : Tendsto (fun _ : ℕ => ((P A).toReal : ℂ) * (∫ ω, Φ 0 ω ∂P)) atTop
        (𝓝 (((P A).toReal : ℂ) * (∫ ω, Φ 0 ω ∂P))) := tendsto_const_nhds
    have hEq_fun : (fun N : ℕ => ∫ ω in A, Φ (τN N ω) ω ∂P) =
        fun _ : ℕ => ((P A).toReal : ℂ) * (∫ ω, Φ 0 ω ∂P) := funext hStepN
    rw [hEq_fun] at hDCT
    have hRes := tendsto_nhds_unique hDCT hConst
    simpa [Φ] using hRes
  -- Step 2: Conclude finite-dimensional marginals of Xtilde on A match X
  have hFD_eval : ∀ (m : ℕ) (v : Fin m → ℝ≥0) (S : Set (Fin m → ℝ)), MeasurableSet S →
      P (A ∩ (fun ω (i : Fin m) => Xtilde (v i) ω) ⁻¹' S) =
        P A * P ((fun ω (i : Fin m) => X (v i) ω) ⁻¹' S) := by
    intro m v S hS
    let Tfin : Finset ℝ≥0 := Finset.univ.image v ∪ {0}
    have h0_mem : (0 : ℝ≥0) ∈ Tfin := by simp [Tfin]
    have hCard_pos : 0 < Tfin.card := Finset.card_pos.mpr ⟨0, h0_mem⟩
    let d : ℕ := Tfin.card - 1
    have hCard : Tfin.card = d + 1 := (Nat.sub_add_cancel hCard_pos).symm
    let uEmb : Fin (d + 1) ↪o ℝ≥0 := Tfin.orderEmbOfFin hCard
    have hu0 : uEmb 0 = 0 := by
      have hmem0 : (0 : ℝ≥0) ∈ Set.range uEmb := by
        rw [Finset.range_orderEmbOfFin]; exact h0_mem
      obtain ⟨k, hk⟩ := hmem0
      exact le_antisymm (by rw [← hk]; exact uEmb.monotone (Fin.zero_le k)) zero_le
    have hv_idx : ∀ i : Fin m, ∃ k : Fin (d + 1), uEmb k = v i := fun i => by
      have hm : v i ∈ Set.range uEmb := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      exact hm
    choose idx hidx using hv_idx
    let L : EuclideanSpace ℝ (Fin d) → (Fin m → ℝ) := fun w i =>
      ∑ j : Fin (idx i).1, w.ofLp ⟨j.1, by omega⟩
    have hL_meas : Measurable L :=
      measurable_pi_lambda _ fun i =>
        Finset.measurable_sum _ fun j _ =>
          (continuous_apply _).measurable.comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).measurable
    have hRec : ∀ (Y : ℝ≥0 → Ω → ℝ), (∀ ω, Y 0 ω = 0) → ∀ ω i,
        L (WithLp.toLp 2 (fun j : Fin d => Y (uEmb j.succ) ω - Y (uEmb j.castSucc) ω)) i = Y (v i) ω := by
      intro Y hY0 ω i
      rw [← hidx i]
      dsimp only [L]
      have hTel : ∀ k : ℕ, (hk : k ≤ d) →
          (∑ j : Fin k, (Y (uEmb ⟨j.1 + 1, by omega⟩) ω - Y (uEmb ⟨j.1, by omega⟩) ω)) =
            Y (uEmb ⟨k, Nat.lt_succ_of_le hk⟩) ω := by
        intro k
        induction k with
        | zero => intro _; simp [hu0, hY0 ω]
        | succ k ih =>
            intro hk
            rw [Fin.sum_univ_castSucc]; simp only [Fin.coe_castSucc, Fin.val_last]; rw [ih (Nat.le_of_succ_le hk)]
            simp [Fin.castSucc]
      exact hTel (idx i).1 (Nat.lt_succ_iff.mp (idx i).2)
    have hEq_meas := hFD_law d uEmb hu0 uEmb.monotone
    have hEval := congrArg (fun μ => μ (L ⁻¹' S)) hEq_meas
    have hΔt_meas : Measurable (fun ω => WithLp.toLp 2 (fun j : Fin d => Xtilde (uEmb j.succ) ω - Xtilde (uEmb j.castSucc) ω)) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp
        (measurable_pi_lambda _ fun j => (hXtilde_meas _).sub (hXtilde_meas _))
    have hΔ0_meas : Measurable (fun ω => WithLp.toLp 2 (fun j : Fin d => X (uEmb j.succ) ω - X (uEmb j.castSucc) ω)) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp
        (measurable_pi_lambda _ fun j => (hMeas _).sub (hMeas _))
    rw [Measure.map_apply hΔt_meas (hL_meas hS), Measure.restrict_apply (hΔt_meas (hL_meas hS)),
      Measure.smul_apply, smul_eq_mul, Measure.map_apply hΔ0_meas (hL_meas hS)] at hEval
    have hPre1 : (fun ω => WithLp.toLp 2 (fun j : Fin d => Xtilde (uEmb j.succ) ω - Xtilde (uEmb j.castSucc) ω)) ⁻¹' (L ⁻¹' S) =
        (fun ω (i : Fin m) => Xtilde (v i) ω) ⁻¹' S := by
      ext ω; simp only [Set.mem_preimage]
      have hXtilde0 : ∀ ω', Xtilde 0 ω' = 0 := fun ω' => by simp [Xtilde]
      have hFun : L (WithLp.toLp 2 (fun j : Fin d => Xtilde (uEmb j.succ) ω - Xtilde (uEmb j.castSucc) ω)) =
          fun i => Xtilde (v i) ω := funext (hRec Xtilde hXtilde0 ω)
      rw [hFun]
    have hPre2 : (fun ω => WithLp.toLp 2 (fun j : Fin d => X (uEmb j.succ) ω - X (uEmb j.castSucc) ω)) ⁻¹' (L ⁻¹' S) =
        (fun ω (i : Fin m) => X (v i) ω) ⁻¹' S := by
      ext ω; simp only [Set.mem_preimage]
      have hFun : L (WithLp.toLp 2 (fun j : Fin d => X (uEmb j.succ) ω - X (uEmb j.castSucc) ω)) =
          fun i => X (v i) ω := funext (hRec X hX0_all ω)
      rw [hFun]
    rw [hPre1, hPre2, Set.inter_comm] at hEval
    exact hEval
  -- Step 3: Deduce P(A ∩ {T(s+h) - T(s) < a}) = P(A) * P({T(h) < a})
  by_cases ha : a ≤ 0
  · have hNull1 : P (A ∩ {ω | T (s + h) ω - T s ω < a}) = 0 := by
      refine measure_mono_null Set.inter_subset_right ?_
      have hAE : ∀ᵐ ω ∂P, ¬ (T (s + h) ω - T s ω < a) := by
        filter_upwards [hFin_s, hFin_sh] with ω hfin_s hfin_sh
        rw [not_lt]
        cases hval : Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
        | top => exact absurd hval hfin_s
        | coe τ =>
            have hsh := (firstUpperPassage_val_and_shift X ω (hCont ω) (hX0_all ω) (s : ℝ)
              (NNReal.coe_pos.mpr hs) τ hval).2.2 (h : ℝ) (NNReal.coe_pos.mpr hh)
            have hsh' : Kyprianou.Ch01.firstUpperPassage X ((s + h : ℝ≥0) : ℝ) ω =
                (τ : WithTop ℝ≥0) + Kyprianou.Ch01.firstUpperPassage (fun u ω' => X (τ + u) ω' - X τ ω') (h : ℝ) ω := by
              push_cast; exact hsh
            cases hval2 : Kyprianou.Ch01.firstUpperPassage (fun u ω' => X (τ + u) ω' - X τ ω') (h : ℝ) ω with
            | top =>
                rw [hval2, WithTop.add_top] at hsh'
                exact absurd hsh' hfin_sh
            | coe δ =>
                rw [hval2, ← WithTop.coe_add] at hsh'
                dsimp only [T]
                rw [if_neg (add_pos hs hh).ne', if_neg hs.ne', hval, hsh']
                simp only [NNReal.coe_add]
                linarith [δ.2]
      have hEq_s : {ω | ¬ ¬ (T (s + h) ω - T s ω < a)} = {ω | T (s + h) ω - T s ω < a} := by ext ω; simp
      rw [← hEq_s]; exact ae_iff.mp hAE
    have hNull2 : P {ω | T h ω < a} = 0 := by
      have hsub : {ω | T h ω < a} = ∅ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        dsimp only [T]; rw [if_neg hh.ne']
        cases Kyprianou.Ch01.firstUpperPassage X (h : ℝ) ω with
        | top => exact ha
        | coe t => exact le_trans ha t.2
      rw [hsub, measure_empty]
    rw [hNull1, hNull2, mul_zero]
  · have ha_pos : 0 < a := lt_of_not_ge ha
    let aNN : ℝ≥0 := ⟨a, ha_pos.le⟩
    let Q_a := {q : ℚ // 0 < q ∧ (q : ℝ) < a}
    obtain ⟨q0, hq0_pos, hq0_lt⟩ := exists_rat_btwn ha_pos
    haveI : Nonempty Q_a := ⟨⟨q0, by exact_mod_cast hq0_pos, hq0_lt⟩⟩
    obtain ⟨enum, henum_surj⟩ := exists_surjective_nat Q_a
    let rOf : Q_a → ℝ≥0 := fun q => ⟨(q.1 : ℝ), by exact_mod_cast q.2.1.le⟩
    let U_tilde : ℕ → Set Ω := fun N =>
      A ∩ (fun ω (i : Fin (N + 1)) => Xtilde (rOf (enum i.1)) ω) ⁻¹'
        {w : Fin (N + 1) → ℝ | ∃ i : Fin (N + 1), (h : ℝ) < w i}
    let U_X : ℕ → Set Ω := fun N =>
      (fun ω (i : Fin (N + 1)) => X (rOf (enum i.1)) ω) ⁻¹'
        {w : Fin (N + 1) → ℝ | ∃ i : Fin (N + 1), (h : ℝ) < w i}
    have hS_meas : ∀ N : ℕ, MeasurableSet {w : Fin (N + 1) → ℝ | ∃ i : Fin (N + 1), (h : ℝ) < w i} := fun N => by
      have hEq : {w : Fin (N + 1) → ℝ | ∃ i : Fin (N + 1), (h : ℝ) < w i} =
          ⋃ i : Fin (N + 1), {w | (h : ℝ) < w i} := by ext w; simp
      rw [hEq]
      exact MeasurableSet.iUnion fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
    have hEq_N : ∀ N : ℕ, P (U_tilde N) = P A * P (U_X N) := fun N =>
      hFD_eval (N + 1) (fun i => rOf (enum i.1)) _ (hS_meas N)
    have hMono_tilde : Monotone U_tilde := fun m n hmn ω hω => by
      refine ⟨hω.1, ?_⟩
      obtain ⟨i, hi⟩ := hω.2
      exact ⟨⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.add_le_add_right hmn 1)⟩, hi⟩
    have hMono_X : Monotone U_X := fun m n hmn ω hω => by
      obtain ⟨i, hi⟩ := hω
      exact ⟨⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.add_le_add_right hmn 1)⟩, hi⟩
    let S_tgt : Set Ω := A ∩ {ω | T (s + h) ω - T s ω < a}
    have hUnion_tilde_ae : (⋃ N : ℕ, U_tilde N) =ᵐ[P] S_tgt := by
      filter_upwards [hFin_s, hFin_sh] with ω hfin_s hfin_sh
      change (ω ∈ ⋃ N : ℕ, U_tilde N) = (ω ∈ S_tgt)
      dsimp only [S_tgt]
      apply propext
      rw [Set.mem_inter_iff, Set.mem_setOf_eq]
      have hDiff_iff : T (s + h) ω - T s ω < a ↔
          Kyprianou.Ch01.firstUpperPassage Xtilde (h : ℝ) ω < (aNN : WithTop ℝ≥0) := by
        cases hval : Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω with
        | top => exact absurd hval hfin_s
        | coe τ =>
            have hτR_eq : τR ω = τ := by dsimp only [τR]; rw [hval]
            have hsh := (firstUpperPassage_val_and_shift X ω (hCont ω) (hX0_all ω) (s : ℝ)
              (NNReal.coe_pos.mpr hs) τ hval).2.2 (h : ℝ) (NNReal.coe_pos.mpr hh)
            have hsh' : Kyprianou.Ch01.firstUpperPassage X ((s + h : ℝ≥0) : ℝ) ω =
                (τ : WithTop ℝ≥0) + Kyprianou.Ch01.firstUpperPassage Xtilde (h : ℝ) ω := by
              have hEq_path : Kyprianou.Ch01.firstUpperPassage Xtilde (h : ℝ) ω =
                  Kyprianou.Ch01.firstUpperPassage (fun u ω' => X (τ + u) ω' - X τ ω') (h : ℝ) ω := by
                dsimp only [Kyprianou.Ch01.firstUpperPassage, Xtilde]
                by_cases hex : ∃ t : ℝ≥0, 0 < t ∧ (h : ℝ) < X (τ + t) ω - X τ ω
                · have hex' : ∃ t : ℝ≥0, 0 < t ∧ (h : ℝ) < X (τR ω + t) ω - X (τR ω) ω := by
                    simpa only [hτR_eq] using hex
                  rw [if_pos hex', if_pos hex]
                  congr 2; ext t; rw [hτR_eq]
                · have hex' : ¬ ∃ t : ℝ≥0, 0 < t ∧ (h : ℝ) < X (τR ω + t) ω - X (τR ω) ω := by
                    simpa only [hτR_eq] using hex
                  rw [if_neg hex', if_neg hex]
              rw [hEq_path]; push_cast; exact hsh
            cases hval2 : Kyprianou.Ch01.firstUpperPassage Xtilde (h : ℝ) ω with
            | top =>
                rw [hval2, WithTop.add_top] at hsh'
                exact absurd hsh' hfin_sh
            | coe δ =>
                rw [hval2, ← WithTop.coe_add] at hsh'
                dsimp only [T]
                rw [if_neg (add_pos hs hh).ne', if_neg hs.ne', hval, hsh']
                simp only [NNReal.coe_add, add_sub_cancel_left, WithTop.coe_lt_coe]
                change (δ : ℝ) < a ↔ δ < aNN
                rw [← NNReal.coe_lt_coe]; rfl
      rw [hDiff_iff, firstUpperPassage_lt_iff_rat Xtilde hXtilde_cont (h : ℝ) aNN ω]
      constructor
      · rintro ⟨_, ⟨N, rfl⟩, hωA, ⟨i, hi⟩⟩
        exact ⟨hωA, ⟨enum i.1, hi⟩⟩
      · rintro ⟨hωA, ⟨q, hq⟩⟩
        obtain ⟨N, hN⟩ := henum_surj q
        refine Set.mem_iUnion.mpr ⟨N, hωA, ⟨Fin.last N, ?_⟩⟩
        change (h : ℝ) < Xtilde (rOf (enum N)) ω
        rw [hN]; exact hq
    have hUnion_X_ae : (⋃ N : ℕ, U_X N) =ᵐ[P] {ω | T h ω < a} := by
      filter_upwards [hFin_h] with ω hfin_h
      change (ω ∈ ⋃ N : ℕ, U_X N) = (ω ∈ {ω | T h ω < a})
      apply propext
      have hTh_iff : T h ω < a ↔
          Kyprianou.Ch01.firstUpperPassage X (h : ℝ) ω < (aNN : WithTop ℝ≥0) := by
        cases hval : Kyprianou.Ch01.firstUpperPassage X (h : ℝ) ω with
        | top => exact absurd hval hfin_h
        | coe δ =>
            dsimp only [T]
            rw [if_neg hh.ne', hval]
            simp only [WithTop.coe_lt_coe]
            change (δ : ℝ) < a ↔ δ < aNN
            rw [← NNReal.coe_lt_coe]; rfl
      rw [Set.mem_setOf_eq, hTh_iff, firstUpperPassage_lt_iff_rat X hCont (h : ℝ) aNN ω]
      constructor
      · rintro ⟨_, ⟨N, rfl⟩, ⟨i, hi⟩⟩
        exact ⟨enum i.1, hi⟩
      · rintro ⟨q, hq⟩
        obtain ⟨N, hN⟩ := henum_surj q
        refine Set.mem_iUnion.mpr ⟨N, ⟨Fin.last N, ?_⟩⟩
        change (h : ℝ) < X (rOf (enum N)) ω
        rw [hN]; exact hq
    change P S_tgt = P A * P {ω | T h ω < a}
    rw [← measure_congr hUnion_tilde_ae, ← measure_congr hUnion_X_ae]
    have hL1 := tendsto_measure_iUnion_atTop (μ := P) hMono_tilde
    have hL2 := ENNReal.Tendsto.const_mul (tendsto_measure_iUnion_atTop (μ := P) hMono_X) (Or.inr (measure_ne_top P A))
    exact tendsto_nhds_unique (hL1.congr hEq_N) hL2

private lemma strongMarkov_firstUpperPassage_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hL : ProbabilityTheory.IsLevyProcess X P)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hCont : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ≥0) (hs : 0 < s)
    (hFin_s : ∀ᵐ ω ∂P, Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω ≠ ⊤)
    (A : Set Ω) (hA_meas : MeasurableSet A)
    (hA_stop : ∀ t : ℝ≥0, @MeasurableSet Ω (Kyprianou.Ch01.naturalSigma X t)
      (A ∩ {ω | Kyprianou.Ch01.firstUpperPassage X (s : ℝ) ω < (t : WithTop ℝ≥0)})) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun u ω =>
        if u = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage X (u : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    ∀ (h : ℝ≥0) (hh : 0 < h),
      (∀ᵐ ω ∂P, Kyprianou.Ch01.firstUpperPassage X ((s + h : ℝ≥0) : ℝ) ω ≠ ⊤) →
      (∀ᵐ ω ∂P, Kyprianou.Ch01.firstUpperPassage X (h : ℝ) ω ≠ ⊤) →
      ∀ (a : ℝ),
        P (A ∩ {ω | T (s + h) ω - T s ω ≤ a}) = P A * P {ω | T h ω ≤ a} := by
  intro T h hh hFin_sh hFin_h a
  have hT_meas : ∀ u : ℝ≥0, Measurable (T u) := fun u =>
    Kyprianou.Ch01.zeroBoundaryPassageClockMeasurableV1 X hMeas hCont u
  have hlt := strongMarkov_firstUpperPassage_lt P X hL hMeas hCont s hs hFin_s A hA_meas hA_stop h hh hFin_sh hFin_h
  let E1 : ℕ → Set Ω := fun n => A ∩ {ω | T (s + h) ω - T s ω < a + 1 / ((n : ℝ) + 1)}
  let E2 : ℕ → Set Ω := fun n => {ω | T h ω < a + 1 / ((n : ℝ) + 1)}
  have hInter1 : (⋂ n : ℕ, E1 n) = A ∩ {ω | T (s + h) ω - T s ω ≤ a} := by
    ext ω; simp only [E1, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hall
      refine ⟨(hall 0).1, le_of_forall_pos_le_add fun ε hε => ?_⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      linarith [(hall n).2]
    · rintro ⟨hωA, hle⟩ n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨hωA, by linarith⟩
  have hInter2 : (⋂ n : ℕ, E2 n) = {ω | T h ω ≤ a} := by
    ext ω; simp only [E2, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hall
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      linarith [hall n]
    · intro hle n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hAnti1 : Antitone E1 := fun m n hmn ω hω => by
    refine ⟨hω.1, ?_⟩
    change T (s + h) ω - T s ω < a + 1 / ((m : ℝ) + 1)
    have hlt_n : T (s + h) ω - T s ω < a + 1 / ((n : ℝ) + 1) := hω.2
    have h1 : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) h1
    linarith
  have hAnti2 : Antitone E2 := fun m n hmn ω hω => by
    change T h ω < a + 1 / ((m : ℝ) + 1)
    have hlt_n : T h ω < a + 1 / ((n : ℝ) + 1) := hω
    have h1 : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) h1
    linarith
  have hLim1 : Tendsto (fun n : ℕ => P (E1 n)) atTop (𝓝 (P (A ∩ {ω | T (s + h) ω - T s ω ≤ a}))) := by
    rw [← hInter1]
    exact tendsto_measure_iInter_atTop (fun n => (hA_meas.inter
      (measurableSet_lt ((hT_meas _).sub (hT_meas _)) measurable_const)).nullMeasurableSet)
      hAnti1 ⟨0, measure_ne_top P _⟩
  have hLim2 : Tendsto (fun n : ℕ => P A * P (E2 n)) atTop (𝓝 (P A * P {ω | T h ω ≤ a})) := by
    rw [← hInter2]
    have h2 := tendsto_measure_iInter_atTop (fun n =>
      (measurableSet_lt (hT_meas h) measurable_const).nullMeasurableSet)
      hAnti2 ⟨0, measure_ne_top P _⟩
    exact (ENNReal.Tendsto.const_mul h2 (Or.inr (measure_ne_top P A)))
  have hEq_seq : (fun n : ℕ => P (E1 n)) = fun n : ℕ => P A * P (E2 n) :=
    funext fun n => hlt (a + 1 / ((n : ℝ) + 1))
  rw [hEq_seq] at hLim1
  exact tendsto_nhds_unique hLim1 hLim2

end StrongMarkovEngine

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : Kyprianou.Ch01.IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s h : ℝ≥0) (hs : 0 < s) (hh : 0 < h) :
    let T : ℝ≥0 → Ω → ℝ :=
      fun u ω =>
        if u = 0 then (0 : ℝ)
        else (match Kyprianou.Ch01.firstUpperPassage X (u : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))
    IdentDistrib (ProbabilityTheory.increment T s (s + h))
      (ProbabilityTheory.increment T 0 h) P P := by
  intro T
  have hT_meas : ∀ u : ℝ≥0, Measurable (T u) := fun u =>
    Kyprianou.Ch01.zeroBoundaryPassageClockMeasurableV1 X hMeas hContinuous u
  have hInc1_meas : Measurable (ProbabilityTheory.increment T s (s + h)) :=
    (hT_meas (s + h)).sub (hT_meas s)
  have hInc2_meas : Measurable (ProbabilityTheory.increment T 0 h) :=
    (hT_meas h).sub (hT_meas 0)
  have hFin_s := Kyprianou.Ch01.inverseGaussianFirstUpperPassageAlmostSureFinitePublic
    P X b (s : ℝ) hb (NNReal.coe_pos.mpr hs) hB hMeas
  have hFin_sh := Kyprianou.Ch01.inverseGaussianFirstUpperPassageAlmostSureFinitePublic
    P X b ((s + h : ℝ≥0) : ℝ) hb (NNReal.coe_pos.mpr (add_pos hs hh)) hB hMeas
  have hFin_h := Kyprianou.Ch01.inverseGaussianFirstUpperPassageAlmostSureFinitePublic
    P X b (h : ℝ) hb (NNReal.coe_pos.mpr hh) hB hMeas
  have hLe := strongMarkov_firstUpperPassage_le P X hB.1 hMeas hContinuous s hs hFin_s
    Set.univ MeasurableSet.univ (fun t => by
      rw [Set.univ_inter]
      exact measurableSet_firstUpperPassage_lt_naturalSigma X hContinuous (s : ℝ) t)
    h hh hFin_sh hFin_h
  refine ⟨hInc1_meas.aemeasurable, hInc2_meas.aemeasurable, ?_⟩
  haveI : IsProbabilityMeasure (P.map (ProbabilityTheory.increment T s (s + h))) :=
    Measure.isProbabilityMeasure_map hInc1_meas.aemeasurable
  haveI : IsProbabilityMeasure (P.map (ProbabilityTheory.increment T 0 h)) :=
    Measure.isProbabilityMeasure_map hInc2_meas.aemeasurable
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply hInc1_meas measurableSet_Iic, Measure.map_apply hInc2_meas measurableSet_Iic]
  have hEq1 : (ProbabilityTheory.increment T s (s + h)) ⁻¹' Set.Iic a =
      Set.univ ∩ {ω | T (s + h) ω - T s ω ≤ a} := by
    ext ω; simp [ProbabilityTheory.increment]
  have hEq2 : (ProbabilityTheory.increment T 0 h) ⁻¹' Set.Iic a = {ω | T h ω ≤ a} := by
    ext ω; simp [ProbabilityTheory.increment, T]
  rw [hEq1, hEq2, hLe a, measure_univ, one_mul]

