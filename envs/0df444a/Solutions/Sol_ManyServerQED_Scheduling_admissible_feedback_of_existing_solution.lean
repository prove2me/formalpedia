-- Prove2me | solution 1 for ManyServerQED.Scheduling.admissible_feedback_of_existing_solution
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T18:35:15.829485+00:00
-- url     : https://prove2.me/submissions/660887e6-7b75-4244-915d-1ae9836529a2

import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_ManyServerQED_Scheduling_feedback_state_measurable
import Theorems.Thm_ManyServerQED_Scheduling_feedback_stopped_primitives_restart

open MeasureTheory Filter Topology
open scoped ENNReal
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

private theorem nat_vector_eventually_constant {k : ℕ} (X : ℝ → Fin k → ℕ) (t : ℝ)
    (hc : ∀ i, ContinuousWithinAt (fun s => (X s i : ℝ)) (Set.Ici t) t) :
    ∀ᶠ s in 𝓝[Set.Ici t] t, X s = X t := by
  have hcoord (i : Fin k) : ∀ᶠ s in 𝓝[Set.Ici t] t, X s i = X t i := by
    have hh : ∀ᶠ s in 𝓝[Set.Ici t] t, dist (X s i : ℝ) (X t i : ℝ) < 1 :=
      Metric.tendsto_nhds.1 (hc i) 1 zero_lt_one
    filter_upwards [hh] with s hs
    rw [Real.dist_eq, abs_lt] at hs
    rcases lt_trichotomy (X s i) (X t i) with h | h | h
    · have hnat : (X s i : ℝ) + 1 ≤ (X t i : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt h)
      linarith [hs.1]
    · exact h
    · have hnat : (X t i : ℝ) + 1 ≤ (X s i : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt h)
      linarith [hs.2]
  exact (Filter.eventually_all.2 hcoord).mono fun s hs => funext hs

private theorem arrival_monotoneOn {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) :
    MonotoneOn (M.A n i ω) (Set.Ici 0) := by
  let e := M.arrivalEpoch n i ω
  let r := M.lamN n i
  have hr : 0 < r := M.lamN_pos n i
  have he (j : ℕ) : e j = partialSum (fun m => M.U i m ω) j / r := by
    simp [e, r, SystemSequence.arrivalEpoch, partialSum, Finset.sum_div]
  have hm : Monotone e := (strictMono_nat_of_lt_succ (fun j => by
    have hj := M.U_pos i (j + 1) ω (by omega)
    rw [he, he]
    apply (div_lt_div_iff_of_pos_right hr).2
    unfold partialSum
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
    linarith)).monotone
  intro a _ b _ hab
  have hcross : ∃ m : ℕ, b < e m := by
    obtain ⟨m, hm⟩ := ((tendsto_atTop.1 (M.U_finite i ω)) (b * r + 1)).exists
    refine ⟨m, ?_⟩
    rw [he, lt_div_iff₀ hr]
    linarith
  obtain ⟨m, hm'⟩ := hcross
  have hfin : renewalCount e b ≠ ⊤ := by
    have hb : renewalCount e b ≤ (m : ℕ∞) := by
      unfold renewalCount
      refine iSup_le (fun j => iSup_le (fun hj => ?_))
      have : j ≤ m := by
        by_contra! h
        exact (not_le_of_gt (hm'.trans_le (hm h.le))) hj
      exact_mod_cast this
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top m) hb
  have hab' : renewalCount e a ≤ renewalCount e b := by
    unfold renewalCount
    exact iSup_le (fun j => iSup_le (fun hj => le_iSup_of_le j (le_iSup_of_le (hj.trans hab) le_rfl)))
  change ((renewalCount e a).toNat : ℝ) ≤ ((renewalCount e b).toNat : ℝ)
  exact_mod_cast ENat.toNat_le_toNat hab' hfin

private theorem monotone_nonnegative_left_limit (f : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Ici 0)) (t : ℝ) (ht : 0 < t) :
    ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l) := by
  let g (s : ℝ) := f (max s 0)
  have hm : Monotone g := fun a b h => hf (le_max_right a 0) (le_max_right b 0) (max_le_max_right 0 h)
  have hl := hm.tendsto_nhdsLT (x := t)
  refine ⟨_, hl.congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsLT ht] with s hs
  dsimp [g]
  rw [max_eq_left hs.1.le]

private theorem state_left_limit {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (X Ψ : Ω → ℝ → Fin k → ℝ)
    (h : M.IsControlled n X0 X Ψ) (ω : Ω) (i : Fin k) (t : ℝ) (ht : 0 < t) :
    ∃ l : ℝ, Tendsto (fun s => X ω s i) (𝓝[<] t) (𝓝 l) := by
  have hiR (s : ℝ) (hs : 0 ≤ s) := (h.integrable ω i s hs).2
  have hiS (s : ℝ) (hs : 0 ≤ s) := (h.integrable ω i s hs).1
  have hRmono := clock_monotone hiR (fun s hs => h.phi_nonneg ω s i hs)
  have hSmono := clock_monotone hiS (fun s hs => h.psi_nonneg ω s i hs)
  have hR0 (s : ℝ) (hs : 0 ≤ s) : 0 ≤ queueTime X Ψ ω i s :=
    intervalIntegral.integral_nonneg hs (fun s hs => h.phi_nonneg ω s i hs.1)
  have hS0 (s : ℝ) (hs : 0 ≤ s) : 0 ≤ busyTime Ψ ω i s :=
    intervalIntegral.integral_nonneg hs (fun s hs => h.psi_nonneg ω s i hs.1)
  have hmR : MonotoneOn (fun s => M.R n i ω (queueTime X Ψ ω i s)) (Set.Ici 0) :=
    fun _ hs _ ht hst => (M.R_poisson n i).mono ω (hR0 _ hs) (hR0 _ ht) (hRmono hs ht hst)
  have hmS : MonotoneOn (fun s => M.S n i ω (busyTime Ψ ω i s)) (Set.Ici 0) :=
    fun _ hs _ ht hst => (M.S_poisson n i).mono ω (hS0 _ hs) (hS0 _ ht) (hSmono hs ht hst)
  obtain ⟨lA, hA⟩ := monotone_nonnegative_left_limit _ (arrival_monotoneOn M n i ω) t ht
  obtain ⟨lR, hR⟩ := monotone_nonnegative_left_limit _ hmR t ht
  obtain ⟨lS, hS⟩ := monotone_nonnegative_left_limit _ hmS t ht
  have hl := ((tendsto_const_nhds (x := (X0 i : ℝ))).add hA).sub hR |>.sub hS
  refine ⟨_, hl.congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsLT ht] with s hs
  exact (h.eq7 ω s i hs.1.le).symm

private theorem nat_values_eventually_constant {α : Type*} (L : Filter α) [NeBot L] (v : α → ℕ)
    (l : ℝ) (hv : Tendsto (fun s => (v s : ℝ)) L (𝓝 l)) :
    ∃ m : ℕ, ∀ᶠ s in L, v s = m := by
  have hc : ∀ᶠ s in L, dist (v s : ℝ) l < 1 / 2 :=
    Metric.tendsto_nhds.1 hv (1 / 2) (by norm_num)
  obtain ⟨s0, hs0⟩ := hc.exists
  refine ⟨v s0, hc.mono fun s hs => ?_⟩
  have hd := dist_triangle (v s : ℝ) l (v s0 : ℝ)
  rw [dist_comm l] at hd
  have hab : |(v s : ℝ) - (v s0 : ℝ)| < 1 := by
    rw [← Real.dist_eq]
    linarith
  rw [abs_lt] at hab
  rcases lt_trichotomy (v s) (v s0) with h | h | h
  · have he : (v s : ℝ) + 1 ≤ (v s0 : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [hab.1]
  · exact h
  · have he : (v s0 : ℝ) + 1 ≤ (v s : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [hab.2]

private theorem feedback_cadlag {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ)
    (F : (Fin k → ℕ) → Fin k → ℝ) (X : Ω → ℝ → Fin k → ℕ)
    (hX : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t => F (X ω t))) :
    ∀ ω i, IsCadlag (fun t => F (X ω t) i) := by
  intro ω i
  constructor
  · intro t ht
    apply tendsto_nhds_of_eventually_eq
    have h := nat_vector_eventually_constant (X ω) t
      (fun j => state_right_continuous M n X0 _ _ hX ω j t ht)
    exact h.mono (fun s hs => congrArg (fun v => F v i) hs)
  · intro t ht
    have he (j : Fin k) : ∃ m : ℕ, ∀ᶠ s in 𝓝[<] t, X ω s j = m := by
      obtain ⟨l, hl⟩ := state_left_limit M n X0 _ _ hX ω j t ht
      exact nat_values_eventually_constant _ _ l hl
    choose l hl using he
    refine ⟨F l i, tendsto_nhds_of_eventually_eq ?_⟩
    exact (Filter.eventually_all.2 hl).mono (fun s hs => congrArg (fun v => F v i) (funext hs))

private theorem scp_of_measurable_state {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ)
    (F : (Fin k → ℕ) → Fin k → ℝ) (X : Ω → ℝ → Fin k → ℕ)
    (hX : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t => F (X ω t)))
    (hM : ∀ t : ℝ, 0 ≤ t → Measurable (fun ω => X ω t)) :
    let Y : Ω → ℝ → Fin k → ℕ := fun ω t => if 0 ≤ t then X ω t else X0
    M.IsSCP n X0 (fun ω t i => (Y ω t i : ℝ)) (fun ω t => F (Y ω t)) := by
  let Y : Ω → ℝ → Fin k → ℕ := fun ω t => if 0 ≤ t then X ω t else X0
  have hE (ω : Ω) (t : ℝ) (ht : 0 ≤ t) : Y ω t = X ω t := if_pos ht
  have hC : M.IsControlled n X0 (fun ω t i => (Y ω t i : ℝ)) (fun ω t => F (Y ω t)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ω t i ht
      simpa only [hE ω t ht] using hX.psi_int ω t i ht
    · intro ω t i ht
      simpa only [hE ω t ht] using hX.phi_int ω t i ht
    · intro ω t i ht
      simpa only [hE ω t ht] using hX.psi_nonneg ω t i ht
    · intro ω t i ht
      simpa only [hE ω t ht] using hX.phi_nonneg ω t i ht
    · intro ω t ht
      simpa only [hE ω t ht] using hX.servers ω t ht
    · intro ω i t ht
      have hp : Set.EqOn (fun s => F (Y ω s) i) (fun s => F (X ω s) i) (Set.uIoo 0 t) := by
        intro s hs
        rw [Set.uIoo_of_le ht] at hs
        dsimp only
        rw [hE ω s hs.1.le]
      have hq : Set.EqOn (fun s => (Y ω s i : ℝ) - F (Y ω s) i)
          (fun s => (X ω s i : ℝ) - F (X ω s) i) (Set.uIoo 0 t) := by
        intro s hs
        rw [Set.uIoo_of_le ht] at hs
        dsimp only
        rw [hE ω s hs.1.le]
      exact ⟨(intervalIntegrable_congr_uIoo hp).2 (hX.integrable ω i t ht).1,
        (intervalIntegrable_congr_uIoo hq).2 (hX.integrable ω i t ht).2⟩
    · intro ω t i ht
      have hp : busyTime (fun ω t => F (Y ω t)) ω i t =
          busyTime (fun ω t => F (X ω t)) ω i t := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht
        intro s hs
        dsimp only
        rw [hE ω s hs.1.le]
      have hq : queueTime (fun ω t i => (Y ω t i : ℝ)) (fun ω t => F (Y ω t)) ω i t =
          queueTime (fun ω t i => (X ω t i : ℝ)) (fun ω t => F (X ω t)) ω i t := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht
        intro s hs
        dsimp only
        rw [hE ω s hs.1.le]
      rw [hp, hq]
      simpa only [hE ω t ht] using hX.eq7 ω t i ht
  refine ⟨hC, feedback_cadlag M n X0 F Y hC, ?_⟩
  intro t i
  have hf : Measurable (fun v : Fin k → ℕ => F v i) := measurable_of_countable _
  by_cases ht : 0 ≤ t
  · rw [show (fun ω => F (Y ω t) i) = (fun ω => F (X ω t) i) from by
      funext ω
      rw [hE ω t ht]]
    exact hf.comp (hM t ht)
  · simpa only [Y, if_neg ht] using (measurable_const (a := F X0 i) : Measurable (fun _ : Ω => F X0 i))

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (n : ℕ)
    (hn : 1 ≤ n) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → (Fin k → ℕ))
    (hF_le : ∀ X i, F X i ≤ X i) (hF_sum : ∀ X, ∑ i, F X i ≤ n)
    (X : Ω → ℝ → Fin k → ℕ)
    (hX : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ))) :
    ∃ Y : Ω → ℝ → Fin k → ℕ,
      (∀ ω t, 0 ≤ t → X ω t = Y ω t) ∧
      M.IsSCP n X0 (fun ω t i => (Y ω t i : ℝ)) (fun ω t i => (F (Y ω t) i : ℝ)) ∧
      M.IsAdmissible n (fun ω t i => (Y ω t i : ℝ)) (fun ω t i => (F (Y ω t) i : ℝ)) := by
  let Y : Ω → ℝ → Fin k → ℕ := fun ω t => if 0 ≤ t then X ω t else X0
  have hMeas := feedback_state_measurable M n X0 F hF_le X hX
  have hY := scp_of_measurable_state M n X0 (fun x i => (F x i : ℝ)) X hX hMeas
  have hA := feedback_stopped_primitives_restart M n hn X0 F hF_le hF_sum Y hY
  exact ⟨Y, fun ω t ht => (if_pos ht).symm, hY, hA⟩
