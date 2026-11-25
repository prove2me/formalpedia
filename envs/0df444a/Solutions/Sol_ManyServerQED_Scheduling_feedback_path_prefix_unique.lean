-- Prove2me | solution 1 for ManyServerQED.Scheduling.feedback_path_prefix_unique
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T18:14:18.465393+00:00
-- url     : https://prove2.me/submissions/de3ea19d-cdd6-4bbe-8ac7-aa988219a36e

import Definitions.Def_ManyServerQED_Scheduling_Policy

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

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ)
    (F : (Fin k → ℕ) → Fin k → ℝ) (X Y : Ω → ℝ → Fin k → ℕ)
    (hX : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t => F (X ω t)))
    (hY : M.IsControlled n X0 (fun ω t i => (Y ω t i : ℝ)) (fun ω t => F (Y ω t)))
    (ω ω' : Ω) (T : ℝ)
    (hA : ∀ i s, 0 ≤ s → s ≤ T → M.A n i ω s = M.A n i ω' s)
    (hR : ∀ i s, 0 ≤ s → s ≤ queueTime (fun ω t i => (X ω t i : ℝ))
        (fun ω t => F (X ω t)) ω i T → M.R n i ω s = M.R n i ω' s)
    (hS : ∀ i s, 0 ≤ s → s ≤ busyTime (fun ω t => F (X ω t)) ω i T →
      M.S n i ω s = M.S n i ω' s) :
    ∀ t ∈ Set.Icc 0 T, X ω t = Y ω' t := by
  let U : Set ℝ := {t | t ∈ Set.Icc 0 T ∧ X ω t ≠ Y ω' t}
  have hemp : U = ∅ := by
    by_contra he
    have hne : U.Nonempty := Set.nonempty_iff_ne_empty.mpr he
    have hbelow : BddBelow U := ⟨0, fun _ hs => hs.1.1⟩
    let τ := sInf U
    have ht0 : 0 ≤ τ := le_csInf hne (fun _ hs => hs.1.1)
    have htT : τ ≤ T := by
      obtain ⟨s, hs⟩ := hne
      exact (csInf_le hbelow hs).trans hs.1.2
    have hpre (s : ℝ) (hs : s ∈ Set.Ioo 0 τ) : X ω s = Y ω' s := by
      by_contra hdiff
      exact (not_le_of_gt hs.2) (csInf_le hbelow ⟨⟨hs.1.le, hs.2.le.trans htT⟩, hdiff⟩)
    have htimeS (i : Fin k) : busyTime (fun ω t => F (X ω t)) ω i τ =
        busyTime (fun ω t => F (Y ω t)) ω' i τ :=
      intervalIntegral.integral_congr_Ioo_of_le ht0 fun s hs => by dsimp only; rw [hpre s hs]
    have htimeR (i : Fin k) : queueTime (fun ω t i => (X ω t i : ℝ))
        (fun ω t => F (X ω t)) ω i τ = queueTime (fun ω t i => (Y ω t i : ℝ))
        (fun ω t => F (Y ω t)) ω' i τ :=
      intervalIntegral.integral_congr_Ioo_of_le ht0 fun s hs => by dsimp only; rw [hpre s hs]
    have heq : X ω τ = Y ω' τ := by
      funext i
      apply Nat.cast_injective (R := ℝ)
      rw [hX.eq7 ω τ i ht0, hY.eq7 ω' τ i ht0, ← htimeS i, ← htimeR i, hA i τ ht0 htT]
      have hRe := hR i _ (intervalIntegral.integral_nonneg ht0
        (fun s hs => hX.phi_nonneg ω s i hs.1))
        (clock_monotone (fun t ht => (hX.integrable ω i t ht).2)
          (fun t ht => hX.phi_nonneg ω t i ht) ht0 (ht0.trans htT) htT)
      have hSe := hS i _ (intervalIntegral.integral_nonneg ht0
        (fun s hs => hX.psi_nonneg ω s i hs.1))
        (clock_monotone (fun t ht => (hX.integrable ω i t ht).1)
          (fun t ht => hX.psi_nonneg ω t i ht) ht0 (ht0.trans htT) htT)
      unfold queueTime busyTime
      rw [hRe, hSe]
    have hXr := nat_vector_eventually_constant (X ω) τ
      (fun i => state_right_continuous M n X0 _ _ hX ω i τ ht0)
    have hYr := nat_vector_eventually_constant (Y ω') τ
      (fun i => state_right_continuous M n X0 _ _ hY ω' i τ ht0)
    have hsubset : U ⊆ Set.Ici τ := fun _ hs => csInf_le hbelow hs
    have : NeBot (𝓝[U] τ) := mem_closure_iff_nhdsWithin_neBot.1 (csInf_mem_closure hne hbelow)
    have hle := nhdsWithin_mono τ hsubset
    have hfalse : ∀ᶠ s in 𝓝[U] τ, False := by
      filter_upwards [hXr.filter_mono hle, hYr.filter_mono hle, self_mem_nhdsWithin (s := U)] with
        s hx hy hs
      exact hs.2 (hx.trans (heq.trans hy.symm))
    exact hfalse.exists.choose_spec
  intro t ht
  by_contra h
  have hm : t ∈ U := ⟨ht, h⟩
  rw [hemp] at hm
  exact hm
