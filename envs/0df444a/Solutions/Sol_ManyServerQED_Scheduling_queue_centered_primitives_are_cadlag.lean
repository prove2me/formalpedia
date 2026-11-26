-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_centered_primitives_are_cadlag
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:00:32.322278+00:00
-- url     : https://prove2.me/submissions/5898d9a0-63b8-4845-8104-bf359d66039f

import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem renewal_eq_of_bracket {e : ℕ → ℝ} (he : Monotone e) {s : ℝ} {j : ℕ}
    (hj : e j ≤ s) (hj_succ : s < e (j + 1)) : renewalCount e s = j := by
  unfold renewalCount
  refine le_antisymm (iSup_le fun r => iSup_le fun hr => ?_) (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  have h : r ≤ j := by
    by_contra! hjr
    exact (not_lt_of_ge hr) (hj_succ.trans_le (he hjr))
  exact_mod_cast h

private theorem epoch_measurable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (m : ℕ) :
    Measurable (fun ω => M.arrivalEpoch n i ω m) := by
  unfold SystemSequence.arrivalEpoch partialSum
  exact Finset.measurable_sum _ (fun j _ => (M.U_meas i j).div_const _)

private theorem epoch_strict {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) :
    StrictMono (M.arrivalEpoch n i ω) := by
  apply strictMono_nat_of_lt_succ
  intro j
  unfold SystemSequence.arrivalEpoch partialSum
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
  have hp : 0 < M.U i (j + 1) ω / M.lamN n i :=
    div_pos (M.U_pos i _ ω (by omega)) (M.lamN_pos n i)
  linarith

private theorem epoch_crosses {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) :
    ∃ m : ℕ, t < M.arrivalEpoch n i ω m := by
  obtain ⟨m, hm⟩ := ((tendsto_atTop.1 (M.U_finite i ω)) (t * M.lamN n i + 1)).exists
  refine ⟨m, ?_⟩
  unfold SystemSequence.arrivalEpoch
  rw [show partialSum (fun j => M.U i j ω / M.lamN n i) m =
    partialSum (fun j => M.U i j ω) m / M.lamN n i by simp [partialSum, Finset.sum_div],
    lt_div_iff₀ (M.lamN_pos n i)]
  linarith

private theorem cadlag_rescale {x : ℝ → ℝ} (h : IsCadlag x) {c : ℝ} (hc : 0 < c) :
    IsCadlag (fun t => x (c*t)) := by
  have hmap : Continuous (fun t : ℝ => c*t) := continuous_const.mul continuous_id
  constructor
  · intro t ht
    refine (h.1 (c*t) (mul_nonneg hc.le ht)).comp hmap.continuousWithinAt ?_
    intro u hu
    exact mul_le_mul_of_nonneg_left hu hc.le
  · intro t ht
    obtain ⟨l,hl⟩ := h.2 (c*t) (mul_pos hc ht)
    refine ⟨l,hl.comp ?_⟩
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact hmap.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin (s := Iio t)] with u hu
      exact mul_lt_mul_of_pos_left hu hc


private theorem renewal_cadlag {e : ℕ → ℝ} (he : StrictMono e) (h0 : e 0 = 0)
    (hTop : ∀ t : ℝ, ∃ n, t < e n) : IsCadlag (fun t => ((renewalCount e t).toNat:ℝ)) := by
  classical
  constructor
  · intro t ht
    let b := Nat.find (hTop t)
    have hT : t < e b := Nat.find_spec (hTop t)
    have hb : 0 < b := by
      by_contra! hn
      rw [Nat.eq_zero_of_le_zero hn,h0] at hT
      linarith
    let j := b-1
    have hj : j+1 = b := by dsimp [j]; omega
    have hmin : e j ≤ t := le_of_not_gt (Nat.find_min (hTop t) (by omega : j < b))
    have hct : ((renewalCount e t).toNat : ℝ) = j := by
      rw [renewal_eq_of_bracket he.monotone hmin (hj ▸ hT), ENat.toNat_natCast]
    rw [ContinuousWithinAt,hct]
    refine (tendsto_const_nhds : Tendsto (fun _ : ℝ => (j:ℝ)) (𝓝[Ici t] t) (𝓝 (j:ℝ))).congr' ?_
    have hLt : Iio (e b) ∈ 𝓝[Ici t] t := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)
    filter_upwards [self_mem_nhdsWithin,hLt] with s hs hs'
    rw [renewal_eq_of_bracket he.monotone (hmin.trans hs) (hj ▸ hs'), ENat.toNat_natCast]
  · intro t ht
    have hD : ∃ m, t ≤ e m := (hTop t).imp (fun _ h => h.le)
    let b := Nat.find hD
    have hT : t ≤ e b := Nat.find_spec hD
    have hb : 0 < b := by
      by_contra! hn
      rw [Nat.eq_zero_of_le_zero hn,h0] at hT
      linarith
    let j := b-1
    have hj : j+1 = b := by dsimp [j]; omega
    have hmin : e j < t := lt_of_not_ge (Nat.find_min hD (by omega : j < b))
    refine ⟨(j:ℝ),(tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (j:ℝ)) (𝓝[<] t) (𝓝 (j:ℝ))).congr' ?_⟩
    have hGt : Ioi (e j) ∈ 𝓝[<] t := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hmin)
    filter_upwards [self_mem_nhdsWithin,hGt] with s hs hs'
    rw [renewal_eq_of_bracket he.monotone hs'.le (hj ▸ hs.trans_le hT), ENat.toNat_natCast]

private theorem cadlag_sub_div {f : ℝ → ℝ} (h : IsCadlag f) (a b : ℝ) :
    IsCadlag (fun t => (f t-a*t)/b) := by
  have hA : Continuous (fun t : ℝ => a*t) := continuous_const.mul continuous_id
  constructor
  · intro t ht
    exact ((h.1 t ht).sub hA.continuousWithinAt).div_const b
  · intro t ht
    obtain ⟨l,hl⟩ := h.2 t ht
    exact ⟨(l-a*t)/b,(hl.sub (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).div_const b⟩

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) :
    ∀ n ω i,
      IsCadlag (fun t => M.Ahat n ω t i) ∧ IsCadlag (fun t => M.Shat n ω t i) ∧
        IsCadlag (fun t => M.Rhat n ω t i) := by
  intro n ω i
  have hA : IsCadlag (M.A n i ω) := renewal_cadlag (epoch_strict M n i ω)
    (by simp [SystemSequence.arrivalEpoch,partialSum]) (epoch_crosses M n i ω)
  refine ⟨cadlag_sub_div hA _ _,?_,?_⟩
  · have hn : IsCadlag (fun t => M.S n i ω ((n:ℝ)*t)) := by
      rcases n.eq_zero_or_pos with rfl | hn
      · simpa only [Nat.cast_zero,zero_mul] using
          (show IsCadlag (fun _ : ℝ => M.S 0 i ω 0) from
            ⟨fun _ _ => continuousWithinAt_const,fun _ _ => ⟨_,tendsto_const_nhds⟩⟩)
      · exact cadlag_rescale ((M.S_poisson n i).cadlag ω) (by exact_mod_cast hn)
    exact cadlag_sub_div hn _ _
  · have hn : IsCadlag (fun t => M.R n i ω ((n:ℝ)*t)) := by
      rcases n.eq_zero_or_pos with rfl | hn
      · simpa only [Nat.cast_zero,zero_mul] using
          (show IsCadlag (fun _ : ℝ => M.R 0 i ω 0) from
            ⟨fun _ _ => continuousWithinAt_const,fun _ _ => ⟨_,tendsto_const_nhds⟩⟩)
      · exact cadlag_rescale ((M.R_poisson n i).cadlag ω) (by exact_mod_cast hn)
    exact cadlag_sub_div hn _ _
