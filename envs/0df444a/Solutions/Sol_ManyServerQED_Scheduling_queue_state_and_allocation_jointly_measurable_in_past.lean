-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_state_and_allocation_jointly_measurable_in_past
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:58:29.123234+00:00
-- url     : https://prove2.me/submissions/c3f0bcea-9807-426f-a240-e20b1368ad73

import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Definitions.Def_ManyServerQED_Scheduling_Policy
import Mathlib

open Set MeasureTheory Filter Topology
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

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

private theorem joint_nnreal {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℝ → ℝ)
    (hm : ∀ t, 0 ≤ t → Measurable (fun ω => f ω t))
    (hr : ∀ ω t, 0 ≤ t → ContinuousWithinAt (f ω) (Ici t) t) :
    Measurable (fun z : Ω × ℝ≥0 => f z.1 z.2) := by
  have hh := AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
    (fun t ω => f ω t) (fun (t : ℝ≥0) => hm t t.2) (fun ω (t : ℝ≥0) =>
      ((hr ω t t.2).comp continuous_subtype_val.continuousWithinAt) (fun _ hs => hs))
  exact hh.comp measurable_swap

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hSCP : M.IsSCP n X0 X Ψ)
    (T : ℝ≥0) :
    @Measurable (Ω × ℝ≥0) (Fin k → ℝ)
      (@MeasurableSpace.prod Ω ℝ≥0 (M.pastInfo n X Ψ T) inferInstance)
      inferInstance (fun z => X z.1 (min (z.2:ℝ) T)) ∧
    @Measurable (Ω × ℝ≥0) (Fin k → ℝ)
      (@MeasurableSpace.prod Ω ℝ≥0 (M.pastInfo n X Ψ T) inferInstance)
      inferInstance (fun z => Ψ z.1 (min (z.2:ℝ) T)) := by
  have ht (s : ℝ) (hs : 0 ≤ s) : min s (T:ℝ) ∈ Icc (0:ℝ) T :=
    ⟨le_min hs T.2,min_le_right _ _⟩
  let clip (t : ℝ) := min t (T:ℝ)
  have hclip (s : ℝ) : ContinuousWithinAt clip (Ici s) s :=
    (continuous_id.min continuous_const).continuousWithinAt
  have hmaps (s : ℝ) : MapsTo clip (Ici s) (Ici (clip s)) := by
    intro t h
    exact min_le_min_right (T:ℝ) (mem_Ici.1 h)
  have hXr (ω : Ω) (i : Fin k) (s : ℝ) (hs : 0 ≤ s) :
      ContinuousWithinAt (fun t => X ω (min t (T:ℝ)) i) (Ici s) s :=
    (state_right_continuous M n X0 X Ψ hSCP.controlled ω i (clip s) (ht s hs).1).comp
      (hclip s) (hmaps s)
  have hΨr (ω : Ω) (i : Fin k) (s : ℝ) (hs : 0 ≤ s) :
      ContinuousWithinAt (fun t => Ψ ω (min t (T:ℝ)) i) (Ici s) s :=
    ((hSCP.cadlag ω i).1 (clip s) (ht s hs).1).comp (hclip s) (hmaps s)
  let G : MeasurableSpace Ω := M.pastInfo n X Ψ T
  have hXm (s : ℝ) (hs : 0 ≤ s) (i : Fin k) : Measurable[G] (fun ω => X ω (min s (T:ℝ)) i) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le i (le_iSup₂_of_le (min s (T:ℝ)) (ht s hs) le_sup_right)
  have hΨm (s : ℝ) (hs : 0 ≤ s) (i : Fin k) : Measurable[G] (fun ω => Ψ ω (min s (T:ℝ)) i) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le i (le_iSup₂_of_le (min s (T:ℝ)) (ht s hs) (le_sup_right.trans le_sup_left))
  constructor
  · letI : MeasurableSpace Ω := G
    exact measurable_pi_lambda _ (fun i => joint_nnreal (fun ω s => X ω (min s (T:ℝ)) i)
      (fun s hs => hXm s hs i) (fun ω s hs => hXr ω i s hs))
  · letI : MeasurableSpace Ω := G
    exact measurable_pi_lambda _ (fun i => joint_nnreal (fun ω s => Ψ ω (min s (T:ℝ)) i)
      (fun s hs => hΨm s hs i) (fun ω s hs => hΨr ω i s hs))
