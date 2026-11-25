-- Prove2me | solution 1 for ManyServerQED.Scheduling.feedback_past_restricted_to_primitive_cut
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T18:50:23.827632+00:00
-- url     : https://prove2.me/submissions/eea19d4d-dd5b-4631-ba35-068f8f11ebf5

import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal
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

private theorem frozen_unchanged {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ)
    (F : (Fin k → ℕ) → Fin k → ℝ) (X : Ω → ℝ → Fin k → ℕ)
    (hX : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t => F (X ω t)))
    (ω : Ω) (a b : ℝ) (ha : 0 ≤ a)
    (hA : ∀ t ∈ Set.Icc a b, ∀ i, M.A n i ω t = M.A n i ω a)
    (hR : ∀ t ∈ Set.Icc a b, ∀ i,
      let J := queueTime (fun ω t i => (X ω t i : ℝ)) (fun ω t => F (X ω t)) ω i a
      M.R n i ω (J + (t - a) * ((X ω a i : ℝ) - F (X ω a) i)) = M.R n i ω J)
    (hS : ∀ t ∈ Set.Icc a b, ∀ i,
      let J := busyTime (fun ω t => F (X ω t)) ω i a
      M.S n i ω (J + (t - a) * F (X ω a) i) = M.S n i ω J) :
    ∀ t ∈ Set.Icc a b, X ω t = X ω a := by
  let U : Set ℝ := {t | t ∈ Set.Icc a b ∧ X ω t ≠ X ω a}
  have hnone : U = ∅ := by
    by_contra he
    have hne : U.Nonempty := Set.nonempty_iff_ne_empty.mpr he
    have hbelow : BddBelow U := ⟨a, fun _ hs => hs.1.1⟩
    let τ := sInf U
    have htA : a ≤ τ := le_csInf hne (fun _ hs => hs.1.1)
    have htB : τ ≤ b := by
      obtain ⟨s, hs⟩ := hne
      exact (csInf_le hbelow hs).trans hs.1.2
    have ht0 : 0 ≤ τ := ha.trans htA
    have hpre (s : ℝ) (hs : s ∈ Set.Ioo a τ) : X ω s = X ω a := by
      by_contra hdiff
      exact (not_le_of_gt hs.2) (csInf_le hbelow ⟨⟨hs.1.le, hs.2.le.trans htB⟩, hdiff⟩)
    have hclock {f c : ℝ → ℝ} (hfa : IntervalIntegrable f volume 0 a)
        (hfτ : IntervalIntegrable f volume 0 τ)
        (hc : ∀ s ∈ Set.Ioo a τ, f s = c a) :
        (∫ s in (0 : ℝ)..τ, f s) = (∫ s in (0 : ℝ)..a, f s) + (τ - a) * c a := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hfa (hfa.symm.trans hfτ)]
      rw [intervalIntegral.integral_congr_Ioo_of_le htA hc, intervalIntegral.integral_const, smul_eq_mul]
    have hbusy (i : Fin k) : busyTime (fun ω t => F (X ω t)) ω i τ =
        busyTime (fun ω t => F (X ω t)) ω i a + (τ - a) * F (X ω a) i := by
      exact hclock (c := fun s => F (X ω s) i) (hX.integrable ω i a ha).1
        (hX.integrable ω i τ ht0).1 (fun s hs => by dsimp only; rw [hpre s hs])
    have hqueue (i : Fin k) : queueTime (fun ω t i => (X ω t i : ℝ)) (fun ω t => F (X ω t)) ω i τ =
        queueTime (fun ω t i => (X ω t i : ℝ)) (fun ω t => F (X ω t)) ω i a +
          (τ - a) * ((X ω a i : ℝ) - F (X ω a) i) := by
      exact hclock (c := fun s => (X ω s i : ℝ) - F (X ω s) i) (hX.integrable ω i a ha).2
        (hX.integrable ω i τ ht0).2 (fun s hs => by dsimp only; rw [hpre s hs])
    have heq : X ω τ = X ω a := by
      funext i
      apply Nat.cast_injective (R := ℝ)
      rw [hX.eq7 ω τ i ht0, hX.eq7 ω a i ha, hbusy i, hqueue i,
        hA τ ⟨htA, htB⟩ i, hR τ ⟨htA, htB⟩ i, hS τ ⟨htA, htB⟩ i]
    have hright := nat_vector_eventually_constant (X ω) τ
      (fun i => state_right_continuous M n X0 _ _ hX ω i τ ht0)
    have hsubset : U ⊆ Set.Ici τ := fun _ hs => csInf_le hbelow hs
    have : NeBot (𝓝[U] τ) := mem_closure_iff_nhdsWithin_neBot.1 (csInf_mem_closure hne hbelow)
    have hfalse : ∀ᶠ s in 𝓝[U] τ, False := by
      filter_upwards [hright.filter_mono (nhdsWithin_mono τ hsubset), self_mem_nhdsWithin (s := U)]
        with s hs hu
      exact hu.2 (hs.trans heq)
    exact hfalse.exists.choose_spec
  intro t ht
  by_contra h
  have hmem : t ∈ U := ⟨ht, h⟩
  rw [hnone] at hmem
  exact hmem

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

private theorem arrival_joint_measurable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) :
    Measurable (fun z : Ω × ℝ≥0 => M.A n i z.1 z.2) := by
  classical
  let h (z : Ω × ℝ≥0) := epoch_crosses M n i z.1 z.2
  have hf : Measurable (fun z : Ω × ℝ≥0 => Nat.find (h z)) := by
    exact measurable_find h (fun j => measurableSet_lt
      (measurable_snd.coe_nnreal_real) ((epoch_measurable M n i j).comp measurable_fst))
  have he (z : Ω × ℝ≥0) : M.A n i z.1 z.2 = ((Nat.find (h z) - 1 : ℕ) : ℝ) := by
    let b := Nat.find (h z)
    have hb : (z.2 : ℝ) < M.arrivalEpoch n i z.1 b := Nat.find_spec (h z)
    have hb0 : 0 < b := by
      by_contra! hh
      rw [Nat.eq_zero_of_le_zero hh] at hb
      simp [SystemSequence.arrivalEpoch, partialSum] at hb
    let j := b - 1
    have hj : j < b := by omega
    have hj' : j + 1 = b := by dsimp [j]; omega
    have h1 : M.arrivalEpoch n i z.1 j ≤ (z.2 : ℝ) :=
      le_of_not_gt (Nat.find_min (h z) hj)
    have h2 : (z.2 : ℝ) < M.arrivalEpoch n i z.1 (j + 1) := by rwa [hj']
    unfold SystemSequence.A
    rw [renewal_eq_of_bracket (epoch_strict M n i z.1).monotone h1 h2, ENat.toNat_natCast]
  simp_rw [he]
  have hm : Measurable (fun m : ℕ => ((m - 1 : ℕ) : ℝ)) := measurable_of_countable _
  exact hm.comp hf

private theorem next_arrival_joint_measurable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) :
    Measurable (fun z : Ω × ℝ => M.nextArrival n i z.1 z.2) := by
  classical
  let h (z : Ω × ℝ) : ∃ m : ℕ, z.2 ≤ M.arrivalEpoch n i z.1 (m + 1) := by
    obtain ⟨m, hm⟩ := epoch_crosses M n i z.1 z.2
    exact ⟨m, hm.le.trans ((epoch_strict M n i z.1).monotone (Nat.le_succ m))⟩
  have he (z : Ω × ℝ) :
      M.nextArrival n i z.1 z.2 = M.arrivalEpoch n i z.1 ((Nat.find (h z)) + 1) := by
    let b := Nat.find (h z)
    let S : Set ℝ := {s | z.2 ≤ s ∧ ∃ m : ℕ, 1 ≤ m ∧ M.arrivalEpoch n i z.1 m = s}
    have hb : IsLeast S (M.arrivalEpoch n i z.1 (b + 1)) := by
      refine ⟨⟨Nat.find_spec (h z), b + 1, by omega, rfl⟩, ?_⟩
      rintro s ⟨hs, m, hm, rfl⟩
      have hm' : m = (m - 1) + 1 := by omega
      have hmin : b ≤ m - 1 := Nat.find_min' (h z) (by rw [← hm']; exact hs)
      exact (epoch_strict M n i z.1).monotone (by omega)
    exact hb.csInf_eq
  simp_rw [he]
  exact Measurable.find (fun m => (epoch_measurable M n i (m + 1)).comp measurable_fst)
    (fun m => measurableSet_le measurable_snd
      ((epoch_measurable M n i (m + 1)).comp measurable_fst)) h

private theorem poisson_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {a : ℝ} (hN : IsPoissonProcess P N a) :
    Measurable (fun z : Ω × ℝ≥0 => N z.1 z.2) := by
  have hRight (ω : Ω) (t : ℝ≥0) :
      ContinuousWithinAt (fun s : ℝ≥0 => N ω s) (Ici t) t := by
    exact (((hN.cadlag ω).1 t t.2).comp continuous_subtype_val.continuousWithinAt)
      (fun s hs => hs)
  exact (AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
    (fun t ω => N ω t) (fun t => hN.meas t) hRight).comp measurable_swap

private noncomputable def eventScore (a T : ℝ) (g : ℝ → ℝ) (r : ℚ) : ℝ :=
  if a < (r : ℝ) ∧ (r : ℝ) < T ∧ g a < g r then (r : ℝ) else T

private noncomputable def nextEvent (a T : ℝ) (g : ℝ → ℝ) : ℝ :=
  ⨅ r : ℚ, eventScore a T g r

private theorem nextEvent_properties (a T : ℝ) (ha : a ≤ T) (g : ℝ → ℝ)
    (hmono : MonotoneOn g (Icc a T))
    (hflat : ∀ s ∈ Icc a T, ∀ᶠ u in 𝓝[Ici s] s, g u = g s) :
    a ≤ nextEvent a T g ∧ nextEvent a T g ≤ T ∧
      (a < T → a < nextEvent a T g) ∧
      (∀ t ∈ Ico a (nextEvent a T g), g t = g a) ∧
      (nextEvent a T g < T → g a < g (nextEvent a T g)) := by
  let e := nextEvent a T g
  have hscore0 (r : ℚ) : a ≤ eventScore a T g r := by
    unfold eventScore
    split_ifs with h
    · exact h.1.le
    · exact ha
  have hscoreT (r : ℚ) : eventScore a T g r ≤ T := by
    unfold eventScore
    split_ifs with h
    · exact h.2.1.le
    · rfl
  have hbd : BddBelow (range (eventScore a T g)) :=
    ⟨a, by rintro _ ⟨r, rfl⟩; exact hscore0 r⟩
  have hea : a ≤ e := le_ciInf hscore0
  have hep (r : ℚ) : e ≤ eventScore a T g r := ciInf_le hbd r
  have heT : e ≤ T := (hep 0).trans (hscoreT 0)
  have hright (s : ℝ) (hs : s ∈ Icc a T) (hsT : s < T) :
      ∃ b ≤ T, s < b ∧ ∀ u ∈ Ico s b, g u = g s := by
    obtain ⟨b, hb, hbsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (hflat s hs)
    refine ⟨min b T, min_le_right _ _, lt_min hb hsT, fun u hu => ?_⟩
    exact hbsub ⟨hu.1, hu.2.trans_le (min_le_left _ _)⟩
  have haste (haT : a < T) : a < e := by
    obtain ⟨b, hbT, hab, hflat⟩ := hright a ⟨le_rfl, ha⟩ haT
    apply hab.trans_le
    apply le_ciInf
    intro r
    unfold eventScore
    split_ifs with h
    · by_contra! hbr
      exact (lt_irrefl (g a)) (by simpa only [hflat r ⟨h.1.le, hbr⟩] using h.2.2)
    · exact hbT
  have hpre (t : ℝ) (ht : t ∈ Ico a e) : g t = g a := by
    have hat : g a ≤ g t := hmono ⟨le_rfl, ha⟩ ⟨ht.1, ht.2.le.trans heT⟩ ht.1
    by_contra! hne
    obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn ht.2
    have hgt := (lt_of_le_of_ne hat (Ne.symm hne)).trans_le
      (hmono ⟨ht.1, ht.2.le.trans heT⟩ ⟨ht.1.trans hr₁.le, hr₂.le.trans heT⟩ hr₁.le)
    have hval : eventScore a T g r = (r : ℝ) :=
      if_pos ⟨ht.1.trans_lt hr₁, hr₂.trans_le heT, hgt⟩
    exact (not_le_of_gt hr₂) (by simpa only [hval] using hep r)
  have hpost (he : e < T) : g a < g e := by
    have hge : g a ≤ g e := hmono ⟨le_rfl, ha⟩ ⟨hea, he.le⟩ hea
    by_contra! hle
    have heq := le_antisymm hle hge
    obtain ⟨b, hbT, heb, hflat⟩ := hright e ⟨hea, heT⟩ he
    have hbe : b ≤ e := by
      apply le_ciInf
      intro r
      unfold eventScore
      split_ifs with h
      · have her : e ≤ (r : ℝ) := (hep r).trans_eq (if_pos h)
        by_contra! hbr
        exact not_lt_of_ge (le_of_eq ((hflat r ⟨her, hbr⟩).trans heq)) h.2.2
      · exact hbT
    exact (not_le_of_gt heb) hbe
  exact ⟨hea, heT, haste, hpre, hpost⟩

private abbrev ClockSnapshot (k : ℕ) :=
  ℝ × (Fin k → ℕ) × (Fin k → ℝ) × (Fin k → ℝ)

private noncomputable def frozenS {k : ℕ} (F : (Fin k → ℕ) → Fin k → ℕ) (z : ClockSnapshot k)
    (t : ℝ) (i : Fin k) : ℝ :=
  z.2.2.1 i + (t - z.1) * (F z.2.1 i : ℝ)

private noncomputable def frozenR {k : ℕ} (F : (Fin k → ℕ) → Fin k → ℕ) (z : ClockSnapshot k)
    (t : ℝ) (i : Fin k) : ℝ :=
  z.2.2.2 i + (t - z.1) * ((z.2.1 i : ℝ) - F z.2.1 i)

private noncomputable def frozenCounts {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ) (ω : Ω) (z : ClockSnapshot k)
    (s : ℝ) (i : Fin k) : ℝ × ℝ × ℝ :=
  (M.A n i ω s.toNNReal, M.S n i ω (frozenS F z s i).toNNReal,
    M.R n i ω (frozenR F z s i).toNNReal)

private noncomputable def frozenTotal {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ) (ω : Ω) (z : ClockSnapshot k)
    (s : ℝ) : ℝ :=
  ∑ i, ((frozenCounts M n F ω z s i).1 + (frozenCounts M n F ω z s i).2.1 +
    (frozenCounts M n F ω z s i).2.2)

private noncomputable def advance {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (T : ℝ) (ω : Ω) (z : ClockSnapshot k) : ClockSnapshot k :=
  let t := nextEvent z.1 T (frozenTotal M n F ω z)
  (t, fun i =>
    let c := frozenCounts M n F ω z t i
    ⌊(X0 i : ℝ) + c.1 - c.2.1 - c.2.2⌋₊, frozenS F z t, frozenR F z t)

private theorem frozenS_meas {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (F : (Fin k → ℕ) → Fin k → ℕ) {z : Ω → ClockSnapshot k} (hz : Measurable z)
    {t : Ω → ℝ} (ht : Measurable t) (i : Fin k) :
    Measurable (fun ω => frozenS F (z ω) (t ω) i) := by
  have hF : Measurable (fun x : Fin k → ℕ => (F x i : ℝ)) := measurable_of_countable _
  exact (measurable_pi_apply i |>.comp hz.snd.snd.fst).add
    ((ht.sub hz.fst).mul (hF.comp hz.snd.fst))

private theorem frozenR_meas {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (F : (Fin k → ℕ) → Fin k → ℕ) {z : Ω → ClockSnapshot k} (hz : Measurable z)
    {t : Ω → ℝ} (ht : Measurable t) (i : Fin k) :
    Measurable (fun ω => frozenR F (z ω) (t ω) i) := by
  have hF : Measurable (fun x : Fin k → ℕ => (x i : ℝ) - F x i) := measurable_of_countable _
  exact (measurable_pi_apply i |>.comp hz.snd.snd.snd).add
    ((ht.sub hz.fst).mul (hF.comp hz.snd.fst))

private theorem frozenCounts_meas {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    {z : Ω → ClockSnapshot k} (hz : Measurable z) {t : Ω → ℝ} (ht : Measurable t) (i : Fin k) :
    Measurable (fun ω => frozenCounts M n F ω (z ω) (t ω) i) := by
  have hA := (arrival_joint_measurable M n i).comp (measurable_id.prodMk ht.real_toNNReal)
  have hS := (poisson_joint_measurable (M.S_poisson n i)).comp
    (measurable_id.prodMk (frozenS_meas F hz ht i).real_toNNReal)
  have hR := (poisson_joint_measurable (M.R_poisson n i)).comp
    (measurable_id.prodMk (frozenR_meas F hz ht i).real_toNNReal)
  exact hA.prodMk (hS.prodMk hR)

private theorem frozenTotal_meas {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    {z : Ω → ClockSnapshot k} (hz : Measurable z) {t : Ω → ℝ} (ht : Measurable t) :
    Measurable (fun ω => frozenTotal M n F ω (z ω) (t ω)) := by
  exact Finset.measurable_sum _ (fun i _ => by
    have hm := frozenCounts_meas M n F hz ht i
    exact (hm.fst.add hm.snd.fst).add hm.snd.snd)

private theorem advance_meas {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (T : ℝ) {z : Ω → ClockSnapshot k} (hz : Measurable z) :
    Measurable (fun ω => advance M n X0 F T ω (z ω)) := by
  let t ω := nextEvent (z ω).1 T (frozenTotal M n F ω (z ω))
  have ht : Measurable t := by
    apply Measurable.iInf
    intro r
    apply Measurable.ite _ measurable_const measurable_const
    by_cases hr : (r : ℝ) < T
    · simpa only [hr, true_and, Set.ofPred_and] using
        (measurableSet_lt hz.fst (measurable_const (a := (r : ℝ)))).inter
          (measurableSet_lt (frozenTotal_meas M n F hz hz.fst)
            (frozenTotal_meas M n F hz (measurable_const (a := (r : ℝ)))))
    · simp [hr]
  exact ht.prodMk ((measurable_pi_lambda _ (fun i => by
    have hm := frozenCounts_meas M n F hz ht i
    exact ((((measurable_const (a := (X0 i : ℝ))).add hm.fst).sub hm.snd.fst).sub hm.snd.snd).nat_floor)).prodMk
    ((measurable_pi_lambda _ (frozenS_meas F hz ht)).prodMk
      (measurable_pi_lambda _ (frozenR_meas F hz ht))))

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


private theorem nat_cast_right_constant (g : ℝ → ℝ) (t : ℝ)
    (h : ∀ s, ∃ m : ℕ, g s = m) (hc : ContinuousWithinAt g (Ici t) t) :
    ∀ᶠ s in 𝓝[Ici t] t, g s = g t := by
  obtain ⟨m, hm⟩ := h t
  have hh := Metric.tendsto_nhds.1 hc (1 : ℝ) zero_lt_one
  filter_upwards [hh] with s hs
  obtain ⟨j, hj⟩ := h s
  rw [Real.dist_eq, hj, hm, abs_lt] at hs
  rcases lt_trichotomy j m with hlt | heq | hgt
  · have hn : (j : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hlt
    linarith [hs.1]
  · simp [hj, hm, heq]
  · have hn : (m : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hgt
    linarith [hs.2]

private theorem frozenTotal_nat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ) (ω : Ω) (z : ClockSnapshot k)
    (s : ℝ) : ∃ m : ℕ, frozenTotal M n F ω z s = m := by
  have hS (i : Fin k) := (M.S_poisson n i).nat_valued ω (frozenS F z s i).toNNReal
    (NNReal.coe_nonneg _)
  have hR (i : Fin k) := (M.R_poisson n i).nat_valued ω (frozenR F z s i).toNNReal
    (NNReal.coe_nonneg _)
  choose S hS using hS
  choose R hR using hR
  refine ⟨∑ i, ((renewalCount (M.arrivalEpoch n i ω) s.toNNReal).toNat + S i + R i), ?_⟩
  push_cast
  simp only [frozenTotal, frozenCounts, SystemSequence.A, hS, hR]

private theorem frozenTotal_mono {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ z i, F z i ≤ z i) (ω : Ω) (z : ClockSnapshot k) :
    Monotone (frozenTotal M n F ω z) := by
  intro u v huv
  apply Finset.sum_le_sum
  intro i _
  have hA := arrival_monotoneOn M n i ω (NNReal.coe_nonneg u.toNNReal) (NNReal.coe_nonneg v.toNNReal)
    (by exact_mod_cast Real.toNNReal_monotone huv)
  have hs : frozenS F z u i ≤ frozenS F z v i := by
    unfold frozenS
    exact add_le_add_right (mul_le_mul_of_nonneg_right (sub_le_sub_right huv _) (Nat.cast_nonneg _)) _
  have hr : frozenR F z u i ≤ frozenR F z v i := by
    unfold frozenR
    have h0 : (0 : ℝ) ≤ (z.2.1 i : ℝ) - (F z.2.1 i : ℝ) := sub_nonneg.mpr (by exact_mod_cast hF _ _)
    exact add_le_add_right (mul_le_mul_of_nonneg_right (sub_le_sub_right huv _) h0) _
  have hS := (M.S_poisson n i).mono ω (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    (by exact_mod_cast Real.toNNReal_monotone hs)
  have hR := (M.R_poisson n i).mono ω (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    (by exact_mod_cast Real.toNNReal_monotone hr)
  exact add_le_add (add_le_add hA hS) hR

private theorem frozenTotal_right_flat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ z i, F z i ≤ z i) (ω : Ω) (z : ClockSnapshot k)
    (a : ℝ) (ha : a = z.1) (ha0 : 0 ≤ a)
    (hS0 : ∀ i, 0 ≤ z.2.2.1 i) (hR0 : ∀ i, 0 ≤ z.2.2.2 i)
    (s : ℝ) (hs : a ≤ s) :
    ∀ᶠ t in 𝓝[Ici s] s, frozenTotal M n F ω z t = frozenTotal M n F ω z s := by
  have hc i : (0 : ℝ) ≤ (z.2.1 i : ℝ) - (F z.2.1 i : ℝ) := sub_nonneg.mpr (by exact_mod_cast hF _ _)
  have hR (i : Fin k) : Monotone (fun s => frozenR F z s i) := by
    intro u v huv
    unfold frozenR
    exact add_le_add_right (mul_le_mul_of_nonneg_right (sub_le_sub_right huv _) (hc i)) _
  have hS (i : Fin k) : Monotone (fun s => frozenS F z s i) := by
    intro u v huv
    unfold frozenS
    exact add_le_add_right (mul_le_mul_of_nonneg_right (sub_le_sub_right huv _) (Nat.cast_nonneg _)) _
  have hRN (u : ℝ) (hu : a ≤ u) (i : Fin k) : 0 ≤ frozenR F z u i := by
    have hh : 0 ≤ u - z.1 := sub_nonneg.mpr (ha ▸ hu)
    exact add_nonneg (hR0 i) (mul_nonneg hh (hc i))
  have hSN (u : ℝ) (hu : a ≤ u) (i : Fin k) : 0 ≤ frozenS F z u i := by
    have hh : 0 ≤ u - z.1 := sub_nonneg.mpr (ha ▸ hu)
    exact add_nonneg (hS0 i) (mul_nonneg hh (Nat.cast_nonneg _))
  have hterms (i : Fin k) : ContinuousWithinAt (fun t => (frozenCounts M n F ω z t i).1 +
      (frozenCounts M n F ω z t i).2.1 + (frozenCounts M n F ω z t i).2.2) (Ici s) s := by
    have hA := arrival_right_continuous M n i ω s (ha0.trans hs)
    have hS' : ContinuousWithinAt (fun t => M.S n i ω (frozenS F z t i)) (Ici s) s :=
      ContinuousWithinAt.comp (f := fun t : ℝ => frozenS F z t i) (x := s)
        (((M.S_poisson n i).cadlag ω).1 _ (hSN s hs i))
        (show ContinuousWithinAt (fun t => frozenS F z t i) (Ici s) s from
          (show Continuous (fun t => frozenS F z t i) by unfold frozenS; fun_prop).continuousWithinAt)
        (fun t ht => hS i ht)
    have hR' : ContinuousWithinAt (fun t => M.R n i ω (frozenR F z t i)) (Ici s) s :=
      ContinuousWithinAt.comp (f := fun t : ℝ => frozenR F z t i) (x := s)
        (((M.R_poisson n i).cadlag ω).1 _ (hRN s hs i))
        (show ContinuousWithinAt (fun t => frozenR F z t i) (Ici s) s from
          (show Continuous (fun t => frozenR F z t i) by unfold frozenR; fun_prop).continuousWithinAt)
        (fun t ht => hR i ht)
    refine ((hA.add hS').add hR').congr_of_mem (fun t ht => ?_) (mem_Ici.mpr (le_refl s))
    simp only [frozenCounts, Real.coe_toNNReal _ (ha0.trans (hs.trans ht)),
      Real.coe_toNNReal _ (hSN t (hs.trans ht) i), Real.coe_toNNReal _ (hRN t (hs.trans ht) i)]
    rfl
  have hNat (i : Fin k) (t : ℝ) : ∃ m : ℕ,
      (frozenCounts M n F ω z t i).1 + (frozenCounts M n F ω z t i).2.1 +
        (frozenCounts M n F ω z t i).2.2 = m := by
    obtain ⟨ps, hps⟩ := (M.S_poisson n i).nat_valued ω (frozenS F z t i).toNNReal (NNReal.coe_nonneg _)
    obtain ⟨pr, hpr⟩ := (M.R_poisson n i).nat_valued ω (frozenR F z t i).toNNReal (NNReal.coe_nonneg _)
    refine ⟨(renewalCount (M.arrivalEpoch n i ω) t.toNNReal).toNat + ps + pr, ?_⟩
    push_cast
    simp only [frozenCounts, SystemSequence.A, hps, hpr]
  refine (Filter.eventually_all.2 (fun i => nat_cast_right_constant _ s (hNat i) (hterms i))).mono ?_
  intro t ht
  exact Finset.sum_congr rfl (fun i _ => ht i)

private noncomputable def actualSnap {Ω : Type*} {k : ℕ} (F : (Fin k → ℕ) → Fin k → ℕ)
    (X : Ω → ℝ → Fin k → ℕ) (ω : Ω) (t : ℝ) : ClockSnapshot k :=
  (t, X ω t, fun i => busyTime (fun ω t i => (F (X ω t) i : ℝ)) ω i t,
    fun i => queueTime (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)) ω i t)

private noncomputable def actualTotal {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (X : Ω → ℝ → Fin k → ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  frozenTotal M n F ω (actualSnap F X ω t) t

private theorem advance_actual {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ v i, F v i ≤ v i) (X : Ω → ℝ → Fin k → ℕ)
    (hC : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)))
    (ω : Ω) (a T : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ T) :
    let z := advance M n X0 F T ω (actualSnap F X ω a)
    z.1 ∈ Icc a T ∧ z = actualSnap F X ω z.1 ∧
      (z.1 < T → actualTotal M n F X ω a < actualTotal M n F X ω z.1) := by
  let Xr : Ω → ℝ → Fin k → ℝ := fun ω t i => X ω t i
  let Ψ : Ω → ℝ → Fin k → ℝ := fun ω t i => F (X ω t) i
  let Fr : (Fin k → ℕ) → Fin k → ℝ := fun v i => F v i
  let v := actualSnap F X ω a
  let g := frozenTotal M n F ω v
  let b := nextEvent a T g
  have hS0 (i : Fin k) : 0 ≤ busyTime Ψ ω i a :=
    intervalIntegral.integral_nonneg ha0 (fun s hs => hC.psi_nonneg ω s i hs.1)
  have hR0 (i : Fin k) : 0 ≤ queueTime Xr Ψ ω i a :=
    intervalIntegral.integral_nonneg ha0 (fun s hs => hC.phi_nonneg ω s i hs.1)
  have hg := frozenTotal_mono M n F hF ω v
  obtain ⟨hab, hbT, _, hpre, hpost⟩ := nextEvent_properties a T ha g (hg.monotoneOn _)
    (fun s hs => frozenTotal_right_flat M n F hF ω v a rfl ha0 hS0 hR0 s hs.1)
  have hb0 : 0 ≤ b := ha0.trans hab
  have hcounts (t : ℝ) (ht : a ≤ t) (i : Fin k) :
      frozenCounts M n F ω v t i =
        (M.A n i ω t, M.S n i ω (frozenS F v t i), M.R n i ω (frozenR F v t i)) := by
    have hs : 0 ≤ frozenS F v t i := add_nonneg (hS0 i)
      (mul_nonneg (sub_nonneg.mpr ht) (hC.psi_nonneg ω a i ha0))
    have hr : 0 ≤ frozenR F v t i := add_nonneg (hR0 i)
      (mul_nonneg (sub_nonneg.mpr ht) (hC.phi_nonneg ω a i ha0))
    simp [frozenCounts, ha0.trans ht, hs, hr]
  have hsame (t : ℝ) (ht : t ∈ Ico a b) (i : Fin k) :
      frozenCounts M n F ω v t i = frozenCounts M n F ω v a i := by
    have hmono (j : Fin k) :
        (frozenCounts M n F ω v a j).1 ≤ (frozenCounts M n F ω v t j).1 ∧
        (frozenCounts M n F ω v a j).2.1 ≤ (frozenCounts M n F ω v t j).2.1 ∧
        (frozenCounts M n F ω v a j).2.2 ≤ (frozenCounts M n F ω v t j).2.2 := by
      rw [hcounts t ht.1, hcounts a le_rfl]
      have hs : frozenS F v a j ≤ frozenS F v t j := by
        unfold frozenS
        gcongr
        exact ht.1
      have hr : frozenR F v a j ≤ frozenR F v t j := by
        unfold frozenR
        have hp : 0 ≤ (v.2.1 j : ℝ) - (F v.2.1 j : ℝ) := hC.phi_nonneg ω a j ha0
        gcongr
        exact ht.1
      have hs0 : 0 ≤ frozenS F v a j := by simpa [frozenS, v, actualSnap] using hS0 j
      have hr0 : 0 ≤ frozenR F v a j := by simpa [frozenR, v, actualSnap] using hR0 j
      exact ⟨arrival_monotoneOn M n j ω ha0 (ha0.trans ht.1) ht.1,
        (M.S_poisson n j).mono ω hs0 (hs0.trans hs) hs,
        (M.R_poisson n j).mono ω hr0 (hr0.trans hr) hr⟩
    let d (j : Fin k) : ℝ :=
      ((frozenCounts M n F ω v t j).1 + (frozenCounts M n F ω v t j).2.1 +
        (frozenCounts M n F ω v t j).2.2) -
      ((frozenCounts M n F ω v a j).1 + (frozenCounts M n F ω v a j).2.1 +
        (frozenCounts M n F ω v a j).2.2)
    have hd (j : Fin k) : 0 ≤ d j := by dsimp [d]; linarith [(hmono j).1, (hmono j).2.1, (hmono j).2.2]
    have hsum : (∑ j, d j) = 0 := by
      dsimp [d]
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (hpre t ht)
    have hzero : d i = 0 :=
      le_antisymm ((Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)).trans_eq hsum) (hd i)
    dsimp [d] at hzero
    exact Prod.ext (by linarith [(hmono i).1, (hmono i).2.1, (hmono i).2.2])
      (Prod.ext (by linarith [(hmono i).1, (hmono i).2.1, (hmono i).2.2])
        (by linarith [(hmono i).1, (hmono i).2.1, (hmono i).2.2]))
  have hconst (t : ℝ) (ht : t ∈ Ico a b) : X ω t = X ω a := by
    apply frozen_unchanged M n X0 Fr X hC ω a t ha0 _ _ _ t ⟨ht.1, le_rfl⟩
    · intro s hs i
      have hh := hsame s ⟨hs.1, hs.2.trans_lt ht.2⟩ i
      rw [hcounts s hs.1, hcounts a le_rfl] at hh
      exact congrArg Prod.fst hh
    · intro s hs i
      have hh := hsame s ⟨hs.1, hs.2.trans_lt ht.2⟩ i
      rw [hcounts s hs.1, hcounts a le_rfl] at hh
      have he := congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) hh
      simpa [v, frozenR, actualSnap] using he
    · intro s hs i
      have hh := hsame s ⟨hs.1, hs.2.trans_lt ht.2⟩ i
      rw [hcounts s hs.1, hcounts a le_rfl] at hh
      have he := congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) hh
      simpa [v, frozenS, actualSnap] using he
  have hclock {f : ℝ → ℝ} (hf₀ : IntervalIntegrable f volume 0 a)
      (hf₁ : IntervalIntegrable f volume 0 b) (hh : ∀ s ∈ Ioo a b, f s = f a) :
      (∫ s in (0 : ℝ)..b, f s) = (∫ s in (0 : ℝ)..a, f s) + (b - a) * f a := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hf₀ (hf₀.symm.trans hf₁)]
    rw [intervalIntegral.integral_congr_Ioo_of_le hab hh, intervalIntegral.integral_const, smul_eq_mul]
  have hbusy (i : Fin k) : busyTime Ψ ω i b = frozenS F v b i :=
    hclock (hC.integrable ω i a ha0).1 (hC.integrable ω i b hb0).1 (fun s hs => by
      dsimp [Ψ]; rw [hconst s ⟨hs.1.le, hs.2⟩])
  have hqueue (i : Fin k) : queueTime Xr Ψ ω i b = frozenR F v b i :=
    hclock (hC.integrable ω i a ha0).2 (hC.integrable ω i b hb0).2 (fun s hs => by
      dsimp [Xr, Ψ]; rw [hconst s ⟨hs.1.le, hs.2⟩])
  have hstate (i : Fin k) : ⌊(X0 i : ℝ) + (frozenCounts M n F ω v b i).1 -
      (frozenCounts M n F ω v b i).2.1 - (frozenCounts M n F ω v b i).2.2⌋₊ = X ω b i := by
    rw [hcounts b hab, ← hbusy i, ← hqueue i]
    rw [show (X0 i : ℝ) + M.A n i ω b - M.S n i ω (busyTime Ψ ω i b) -
      M.R n i ω (queueTime Xr Ψ ω i b) = X ω b i from by
      have he := hC.eq7 ω b i hb0
      change (X ω b i : ℝ) = _ at he
      linarith]
    exact Nat.floor_natCast _
  change b ∈ Icc a T ∧ advance M n X0 F T ω v = actualSnap F X ω b ∧
    (b < T → actualTotal M n F X ω a < actualTotal M n F X ω b)
  refine ⟨⟨hab, hbT⟩, ?_, ?_⟩
  · apply Prod.ext
    · rfl
    · exact Prod.ext (funext hstate) (Prod.ext (funext fun i => (hbusy i).symm)
        (funext fun i => (hqueue i).symm))
  · intro h
    have htot : g b = actualTotal M n F X ω b := by
      unfold g frozenTotal actualTotal
      apply Finset.sum_congr rfl
      intro i _
      rw [hcounts b hab, ← hbusy i, ← hqueue i]
      simp only [frozenCounts, frozenS, frozenR, actualSnap, sub_self, zero_mul, add_zero,
        Real.coe_toNNReal _ hb0]
      have hs0 : 0 ≤ busyTime Ψ ω i b := intervalIntegral.integral_nonneg hb0
        (fun s hs => hC.psi_nonneg ω s i hs.1)
      have hr0 : 0 ≤ queueTime Xr Ψ ω i b := intervalIntegral.integral_nonneg hb0
        (fun s hs => hC.phi_nonneg ω s i hs.1)
      change _ = M.A n i ω b + M.S n i ω (busyTime Ψ ω i b).toNNReal +
        M.R n i ω (queueTime Xr Ψ ω i b).toNNReal
      rw [Real.coe_toNNReal _ hs0, Real.coe_toNNReal _ hr0]
    rw [← htot]
    exact hpost h

private theorem actualTotal_mono {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (X : Ω → ℝ → Fin k → ℕ)
    (hC : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)))
    (ω : Ω) : MonotoneOn (actualTotal M n F X ω) (Ici 0) := by
  intro s hs t ht hst
  let Xr : Ω → ℝ → Fin k → ℝ := fun ω t i => X ω t i
  let Ψ : Ω → ℝ → Fin k → ℝ := fun ω t i => F (X ω t) i
  have hS0 (u : ℝ) (hu : 0 ≤ u) (i : Fin k) : 0 ≤ busyTime Ψ ω i u :=
    intervalIntegral.integral_nonneg hu (fun s hs => hC.psi_nonneg ω s i hs.1)
  have hR0 (u : ℝ) (hu : 0 ≤ u) (i : Fin k) : 0 ≤ queueTime Xr Ψ ω i u :=
    intervalIntegral.integral_nonneg hu (fun s hs => hC.phi_nonneg ω s i hs.1)
  unfold actualTotal frozenTotal
  apply Finset.sum_le_sum
  intro i _
  have he (u : ℝ) (hu : 0 ≤ u) : frozenCounts M n F ω (actualSnap F X ω u) u i =
      (M.A n i ω u, M.S n i ω (busyTime Ψ ω i u), M.R n i ω (queueTime Xr Ψ ω i u)) := by
    simp only [actualSnap, frozenCounts, frozenS, frozenR, Real.coe_toNNReal _ hu,
      sub_self, zero_mul, add_zero]
    rw [Real.coe_toNNReal _ (hS0 u hu i), Real.coe_toNNReal _ (hR0 u hu i)]
  rw [he s hs, he t ht]
  have hS := clock_monotone (fun u hu => (hC.integrable ω i u hu).1)
    (fun u hu => hC.psi_nonneg ω u i hu) hs ht hst
  have hR := clock_monotone (fun u hu => (hC.integrable ω i u hu).2)
    (fun u hu => hC.phi_nonneg ω u i hu) hs ht hst
  exact add_le_add (add_le_add (arrival_monotoneOn M n i ω hs ht hst)
    ((M.S_poisson n i).mono ω (hS0 s hs i) (hS0 t ht i) hS))
    ((M.R_poisson n i).mono ω (hR0 s hs i) (hR0 t ht i) hR)

private theorem nextEvent_le_T (a T : ℝ) (ha : a ≤ T) (g : ℝ → ℝ) :
    nextEvent a T g ≤ T := by
  have hb : BddBelow (range (eventScore a T g)) := ⟨a, by
    rintro _ ⟨r, rfl⟩
    unfold eventScore
    split_ifs with h
    · exact h.1.le
    · exact ha⟩
  refine (ciInf_le hb (0 : ℚ)).trans ?_
  unfold eventScore
  split_ifs with h
  · exact h.2.1.le
  · exact le_rfl

private theorem nextEvent_ge_a (a T : ℝ) (ha : a ≤ T) (g : ℝ → ℝ) :
    a ≤ nextEvent a T g := by
  apply le_ciInf
  intro r
  unfold eventScore
  split_ifs with h
  · exact h.1.le
  · exact ha

private theorem nextEvent_le_candidate (a T : ℝ) (ha : a ≤ T) (g : ℝ → ℝ)
    (r : ℚ) (hr : a < (r : ℝ)) (hrT : (r : ℝ) < T) (hg : g a < g r) :
    nextEvent a T g ≤ (r : ℝ) := by
  have hb : BddBelow (range (eventScore a T g)) := ⟨a, by
    rintro _ ⟨q, rfl⟩
    unfold eventScore
    split_ifs with h
    · exact h.1.le
    · exact ha⟩
  exact (ciInf_le hb r).trans_eq (if_pos ⟨hr, hrT, hg⟩)

private theorem nextEvent_capped_pair (a T : ℝ) (ha : a ≤ T) (g gc : ℝ → ℝ)
    (hmono : MonotoneOn gc (Icc a T))
    (hsame : g a = gc a) (hle : ∀ s ∈ Icc a T, gc s ≤ g s)
    (hpost : nextEvent a T g < T → g a < g (nextEvent a T g)) :
    nextEvent a T g ≤ nextEvent a T gc ∧
      (g (nextEvent a T g) = gc (nextEvent a T g) → nextEvent a T gc = nextEvent a T g) ∧
      ((∀ s ∈ Icc a (nextEvent a T gc), g s = gc s) →
        nextEvent a T gc = nextEvent a T g) := by
  have h₀ : nextEvent a T g ≤ nextEvent a T gc := by
    apply le_ciInf
    intro r
    unfold eventScore
    split_ifs with h
    · exact nextEvent_le_candidate a T ha g r h.1 h.2.1
        ((hsame ▸ h.2.2).trans_le (hle r ⟨h.1.le, h.2.1.le⟩))
    · exact nextEvent_le_T a T ha g
  refine ⟨h₀, fun he => le_antisymm ?_ h₀, fun h => le_antisymm ?_ h₀⟩
  · by_contra! hlt
    obtain ⟨r, hr, hrt⟩ := exists_rat_btwn hlt
    have hu := nextEvent_le_T a T ha gc
    have hb := nextEvent_ge_a a T ha g
    have hg := hpost (hlt.trans_le hu)
    rw [hsame, he] at hg
    have hgr := hg.trans_le (hmono ⟨hb, (hlt.trans_le hu).le⟩
      ⟨hb.trans hr.le, (hrt.trans_le hu).le⟩ hr.le)
    exact (not_le_of_gt hrt) (nextEvent_le_candidate a T ha gc r
      (hb.trans_lt hr) (hrt.trans_le hu) hgr)
  · by_contra! hlt
    obtain ⟨r, hr, hrt⟩ := exists_rat_btwn hlt
    have hu := nextEvent_le_T a T ha gc
    have hb := nextEvent_ge_a a T ha g
    have hg := hpost (hlt.trans_le hu)
    have he := h _ ⟨hb, hlt.le⟩
    rw [hsame, he] at hg
    have hgr := hg.trans_le (hmono ⟨hb, (hlt.trans_le hu).le⟩
      ⟨hb.trans hr.le, (hrt.trans_le hu).le⟩ hr.le)
    exact (not_le_of_gt hrt) (nextEvent_le_candidate a T ha gc r
      (hb.trans_lt hr) (hrt.trans_le hu) hgr)

private noncomputable def limitArrival {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (ω : Ω) (s : ℝ) (i : Fin k) : ℝ :=
  ∑ j ∈ Finset.range (d i), if M.arrivalEpoch n i ω (j + 1) ≤ s then 1 else 0

private theorem limitArrival_mono {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (ω : Ω) (i : Fin k) :
    Monotone (fun s => limitArrival M n d ω s i) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro j _
  split_ifs with ha hb
  · exact le_rfl
  · exact (hb (ha.trans hab)).elim
  · norm_num
  · exact le_rfl

private theorem limitArrival_eq_min {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (ω : Ω) (s : ℝ) (hs : 0 ≤ s) (i : Fin k) :
    limitArrival M n d ω s i = min (d i : ℝ) (M.A n i ω s) := by
  let e := M.arrivalEpoch n i ω
  have he := epoch_strict M n i ω
  have hzero : e 0 = 0 := by simp [e, SystemSequence.arrivalEpoch, partialSum]
  obtain ⟨b, hb₁, hb₂⟩ := arrival_prefix_index (show e 0 ≤ s by rwa [hzero]) (epoch_crosses M n i ω s)
  have heq : M.A n i ω s = b := by
    unfold SystemSequence.A
    rw [renewal_eq_of_bracket he.monotone hb₁ hb₂, ENat.toNat_natCast]
  have htest (j : ℕ) : e (j + 1) ≤ s ↔ j < b := by
    constructor
    · intro hj
      by_contra! h
      exact (not_le_of_gt (hb₂.trans_le (he.monotone (by omega : b + 1 ≤ j + 1)))) hj
    · intro hj
      exact (he.monotone (by omega : j + 1 ≤ b)).trans hb₁
  unfold limitArrival
  change (∑ j ∈ Finset.range (d i), if e (j+1) ≤ s then 1 else (0 : ℝ)) = _
  simp_rw [htest]
  rw [heq, ← Nat.cast_min]
  have hfil : (Finset.range (d i)).filter (fun j => j < b) = Finset.range (min (d i) b) := by
    ext j
    simp
  rw [← Finset.sum_filter, hfil]
  simp

private theorem limitArrival_eq_of_coverage {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (ω : Ω) (s : ℝ) (hs : 0 ≤ s) (i : Fin k)
    (h : s ≤ M.arrivalEpoch n i ω (d i)) :
    limitArrival M n d ω s i = M.A n i ω s := by
  rw [limitArrival_eq_min M n d ω s hs i, min_eq_right]
  let e := M.arrivalEpoch n i ω
  have he := epoch_strict M n i ω
  have hb : renewalCount e s ≤ (d i : ℕ∞) := by
    unfold renewalCount
    refine iSup_le (fun j => iSup_le (fun hj => ?_))
    have hle : e j ≤ e (d i) := hj.trans h
    exact_mod_cast he.le_iff_le.mp hle
  change ((renewalCount e s).toNat : ℝ) ≤ (d i : ℝ)
  exact_mod_cast ENat.toNat_le_of_le_natCast hb

private noncomputable def limitedCounts {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0)
    (ω : Ω) (z : ClockSnapshot k) (s : ℝ) (i : Fin k) : ℝ × ℝ × ℝ :=
  (limitArrival M n d ω s i, M.S n i ω ((min (frozenS F z s i).toNNReal (p i) : ℝ≥0) : ℝ),
    M.R n i ω ((min (frozenR F z s i).toNNReal (q i) : ℝ≥0) : ℝ))

private noncomputable def limitedTotal {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0)
    (ω : Ω) (z : ClockSnapshot k) (s : ℝ) : ℝ :=
  ∑ i, ((limitedCounts M n F d p q ω z s i).1 + (limitedCounts M n F d p q ω z s i).2.1 +
    (limitedCounts M n F d p q ω z s i).2.2)

private noncomputable def proposal {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (T : ℝ)
    (ω : Ω) (z : ClockSnapshot k) : ClockSnapshot k :=
  let t := nextEvent z.1 T (limitedTotal M n F d p q ω z)
  (t, fun i =>
    let c := limitedCounts M n F d p q ω z t i
    ⌊(X0 i : ℝ) + c.1 - c.2.1 - c.2.2⌋₊, frozenS F z t, frozenR F z t)

private def insideBox {k : ℕ} (p q : Fin k → ℝ≥0) (z : ClockSnapshot k) : Prop :=
  ∀ i, z.2.2.1 i ≤ p i ∧ z.2.2.2 i ≤ q i

private noncomputable def limitedAdvance {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (T : ℝ)
    (ω : Ω) (z : ClockSnapshot k) : ClockSnapshot k := by
  classical
  exact let v := proposal M n X0 F d p q T ω z
  if insideBox p q v then v else z

private theorem frozenS_mono {k : ℕ} (F : (Fin k → ℕ) → Fin k → ℕ)
    (z : ClockSnapshot k) (i : Fin k) : Monotone (fun t => frozenS F z t i) := by
  intro a b hab
  unfold frozenS
  exact add_le_add_right (mul_le_mul_of_nonneg_right (sub_le_sub_right hab _) (Nat.cast_nonneg _)) _

private theorem frozenR_mono {k : ℕ} (F : (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ x i, F x i ≤ x i) (z : ClockSnapshot k) (i : Fin k) :
    Monotone (fun t => frozenR F z t i) := by
  intro a b hab
  have h : 0 ≤ (z.2.1 i : ℝ) - (F z.2.1 i : ℝ) := sub_nonneg.mpr (by exact_mod_cast hF _ _)
  unfold frozenR
  exact add_le_add_right (mul_le_mul_of_nonneg_right (sub_le_sub_right hab _) h) _

private theorem limitedTotal_mono {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ x i, F x i ≤ x i) (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (ω : Ω) (z : ClockSnapshot k) :
    Monotone (limitedTotal M n F d p q ω z) := by
  intro a b hab
  unfold limitedTotal limitedCounts
  apply Finset.sum_le_sum
  intro i _
  have hS := (M.S_poisson n i).mono ω (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    (by exact_mod_cast min_le_min_right (p i) (Real.toNNReal_monotone (frozenS_mono F z i hab)))
  have hR := (M.R_poisson n i).mono ω (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    (by exact_mod_cast min_le_min_right (q i) (Real.toNNReal_monotone (frozenR_mono F hF z i hab)))
  exact add_le_add (add_le_add (limitArrival_mono M n d ω i hab) hS) hR

private theorem limitedTotal_le {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (ω : Ω) (z : ClockSnapshot k) (s : ℝ) (hs : 0 ≤ s) :
    limitedTotal M n F d p q ω z s ≤ frozenTotal M n F ω z s := by
  unfold limitedTotal limitedCounts frozenTotal frozenCounts
  apply Finset.sum_le_sum
  intro i _
  have hA := (limitArrival_eq_min M n d ω s hs i).le.trans (min_le_right _ _)
  have hS := (M.S_poisson n i).mono ω (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    (by exact_mod_cast min_le_left (frozenS F z s i).toNNReal (p i))
  have hR := (M.R_poisson n i).mono ω (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    (by exact_mod_cast min_le_left (frozenR F z s i).toNNReal (q i))
  rw [Real.coe_toNNReal _ hs]
  exact add_le_add (add_le_add hA hS) hR

private theorem limitedCounts_eq {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (ω : Ω) (z : ClockSnapshot k) (s : ℝ) (hs : 0 ≤ s)
    (hA : ∀ i, s ≤ M.arrivalEpoch n i ω (d i))
    (hS : ∀ i, frozenS F z s i ≤ p i) (hR : ∀ i, frozenR F z s i ≤ q i) (i : Fin k) :
    limitedCounts M n F d p q ω z s i = frozenCounts M n F ω z s i := by
  unfold limitedCounts frozenCounts
  rw [limitArrival_eq_of_coverage M n d ω s hs i (hA i), Real.coe_toNNReal _ hs,
    min_eq_left (Real.toNNReal_le_iff_le_coe.mpr (hS i)),
    min_eq_left (Real.toNNReal_le_iff_le_coe.mpr (hR i))]

private theorem limitedAdvance_actual_box {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ v i, F v i ≤ v i) (X : Ω → ℝ → Fin k → ℕ)
    (hC : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)))
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0)
    (ω : Ω) (a T : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ T)
    (hA : ∀ i, T ≤ M.arrivalEpoch n i ω (d i)) (hbox : insideBox p q (actualSnap F X ω a)) :
    let w := limitedAdvance M n X0 F d p q T ω (actualSnap F X ω a)
    w.1 ∈ Icc a T ∧ insideBox p q w ∧ w = actualSnap F X ω w.1 ∧
      (insideBox p q (actualSnap F X ω T) → w = advance M n X0 F T ω (actualSnap F X ω a)) := by
  classical
  let z := actualSnap F X ω a
  let g := frozenTotal M n F ω z
  let gc := limitedTotal M n F d p q ω z
  let e := nextEvent a T g
  let b := nextEvent a T gc
  let v := proposal M n X0 F d p q T ω z
  have heA : a ≤ e := nextEvent_ge_a a T ha g
  have hbA : a ≤ b := nextEvent_ge_a a T ha gc
  have heT : e ≤ T := nextEvent_le_T a T ha g
  have hbT : b ≤ T := nextEvent_le_T a T ha gc
  have hclockS (i : Fin k) : 0 ≤ z.2.2.1 i :=
    intervalIntegral.integral_nonneg ha0 (fun s hs => hC.psi_nonneg ω s i hs.1)
  have hclockR (i : Fin k) : 0 ≤ z.2.2.2 i :=
    intervalIntegral.integral_nonneg ha0 (fun s hs => hC.phi_nonneg ω s i hs.1)
  have hgpost : e < T → g a < g e :=
    (nextEvent_properties a T ha g (frozenTotal_mono M n F hF ω z |>.monotoneOn _)
      (fun s hs => frozenTotal_right_flat M n F hF ω z a rfl ha0 hclockS hclockR s hs.1)).2.2.2.2
  have hcnt (s : ℝ) (hs : s ∈ Icc a T)
      (hsB : ∀ i, frozenS F z s i ≤ p i ∧ frozenR F z s i ≤ q i) (i : Fin k) :
      limitedCounts M n F d p q ω z s i = frozenCounts M n F ω z s i :=
    limitedCounts_eq M n F d p q ω z s (ha0.trans hs.1)
      (fun i => hs.2.trans (hA i)) (fun i => (hsB i).1) (fun i => (hsB i).2) i
  have hgt (s : ℝ) (hs : s ∈ Icc a T)
      (hsB : ∀ i, frozenS F z s i ≤ p i ∧ frozenR F z s i ≤ q i) : g s = gc s := by
    unfold g gc frozenTotal limitedTotal
    exact Finset.sum_congr rfl (fun i _ => by rw [hcnt s hs hsB i])
  have hcenter : g a = gc a := hgt a ⟨le_rfl, ha⟩ (by
    intro i
    simpa [frozenS, frozenR, z, actualSnap] using hbox i)
  have hle := nextEvent_capped_pair a T ha g gc
    (limitedTotal_mono M n F hF d p q ω z |>.monotoneOn _) hcenter
    (fun s hs => limitedTotal_le M n F d p q ω z s (ha0.trans hs.1)) hgpost
  have hsound (hv : insideBox p q v) : v = advance M n X0 F T ω z := by
    have heq : b = e := hle.2.2 (fun s hs => hgt s ⟨hs.1, hs.2.trans hbT⟩ fun i =>
      ⟨(frozenS_mono F z i hs.2).trans (hv i).1,
        (frozenR_mono F hF z i hs.2).trans (hv i).2⟩)
    let stateC (i : Fin k) := let c := limitedCounts M n F d p q ω z b i
      ⌊(X0 i : ℝ) + c.1 - c.2.1 - c.2.2⌋₊
    let stateF (t : ℝ) (i : Fin k) := let c := frozenCounts M n F ω z t i
      ⌊(X0 i : ℝ) + c.1 - c.2.1 - c.2.2⌋₊
    change (b, stateC, frozenS F z b, frozenR F z b) = (e, stateF e, frozenS F z e, frozenR F z e)
    rw [← heq]
    have hh : stateC = stateF b := by
      funext i
      dsimp [stateC, stateF]
      rw [hcnt b ⟨hbA, hbT⟩ hv i]
    rw [hh]
  have hvalid := advance_actual M n X0 F hF X hC ω a T ha0 ha
  change e ∈ Icc a T ∧ advance M n X0 F T ω z = actualSnap F X ω e ∧ _ at hvalid
  have hgood (hgT : insideBox p q (actualSnap F X ω T)) : insideBox p q v := by
    have hbE : ∀ i, frozenS F z e i ≤ p i ∧ frozenR F z e i ≤ q i := by
      have hboxE : insideBox p q (actualSnap F X ω e) := by
        intro i
        have hS := clock_monotone (fun s hs => (hC.integrable ω i s hs).1)
          (fun s hs => hC.psi_nonneg ω s i hs) (ha0.trans heA) (ha0.trans ha) heT
        have hR := clock_monotone (fun s hs => (hC.integrable ω i s hs).2)
          (fun s hs => hC.phi_nonneg ω s i hs) (ha0.trans heA) (ha0.trans ha) heT
        exact ⟨hS.trans (hgT i).1, hR.trans (hgT i).2⟩
      have hboxAdv := hvalid.2.1.symm ▸ hboxE
      exact hboxAdv
    have hb : b = e := hle.2.1 (hgt e ⟨heA, heT⟩ hbE)
    intro i
    change frozenS F z b i ≤ p i ∧ frozenR F z b i ≤ q i
    rw [hb]
    exact hbE i
  change let w := if insideBox p q v then v else z
  w.1 ∈ Icc a T ∧ insideBox p q w ∧ w = actualSnap F X ω w.1 ∧
    (insideBox p q (actualSnap F X ω T) → w = advance M n X0 F T ω z)
  dsimp only
  by_cases hv : insideBox p q v
  · simp only [if_pos hv]
    have hEq := hsound hv
    refine ⟨?_, hv, ?_, fun _ => hEq⟩
    · rw [hEq]
      exact hvalid.1
    · rw [hEq]
      exact hvalid.2.1
  · simp only [if_neg hv]
    exact ⟨⟨le_rfl, ha⟩, hbox, rfl, fun h => (hv (hgood h)).elim⟩

private noncomputable abbrev primitiveCutInfo {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) : MeasurableSpace Ω :=
  (⨆ (i : Fin k) (j : ℕ) (_ : j < d i), MeasurableSpace.comap (M.U i (j+1)) inferInstance) ⊔
    (⨆ (i : Fin k) (u : ℝ≥0) (_ : u ≤ p i), MeasurableSpace.comap (fun ω => M.S n i ω u) inferInstance) ⊔
    (⨆ (i : Fin k) (u : ℝ≥0) (_ : u ≤ q i), MeasurableSpace.comap (fun ω => M.R n i ω u) inferInstance)

private theorem cut_epoch_meas {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (p q : Fin k → ℝ≥0)
    (i : Fin k) (j : ℕ) (hj : j ≤ d i) :
    Measurable[primitiveCutInfo M n d p q] (fun ω => M.arrivalEpoch n i ω j) := by
  unfold SystemSequence.arrivalEpoch partialSum
  apply Finset.measurable_sum
  intro m hm
  apply Measurable.div_const
  obtain ⟨hm1, hmj⟩ := Finset.mem_Icc.mp hm
  apply measurable_iff_comap_le.2
  have he : m - 1 + 1 = m := by omega
  rw [← he]
  refine (le_iSup_of_le i (le_iSup_of_le (m - 1) ?_)).trans (le_sup_left.trans le_sup_left)
  exact le_iSup (fun _ : m - 1 < d i => MeasurableSpace.comap (M.U i (m - 1 + 1)) inferInstance)
    (by omega)

private theorem cut_arrival_meas {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (p q : Fin k → ℝ≥0)
    {t : Ω → ℝ} (ht : Measurable[primitiveCutInfo M n d p q] t) (i : Fin k) :
    Measurable[primitiveCutInfo M n d p q] (fun ω => limitArrival M n d ω (t ω) i) := by
  unfold limitArrival
  apply Finset.measurable_sum
  intro j hj
  have h := Finset.mem_range.mp hj
  exact Measurable.ite (measurableSet_le (cut_epoch_meas M n d p q i (j + 1) (by omega)) ht)
    measurable_const measurable_const

private theorem capped_poisson_eval_meas {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {rate : ℝ} (hN : IsPoissonProcess P N rate)
    (G : MeasurableSpace Ω) (cap : ℝ≥0)
    (hm : ∀ u : ℝ≥0, u ≤ cap → Measurable[G] (fun ω => N ω u))
    {t : Ω → ℝ} (ht : Measurable[G] t) :
    Measurable[G] (fun ω => N ω ((min (t ω).toNNReal cap : ℝ≥0) : ℝ)) := by
  have hRight (ω : Ω) (u : ℝ≥0) :
      ContinuousWithinAt (fun s : ℝ≥0 => N ω ((min s cap : ℝ≥0) : ℝ)) (Ici u) u := by
    let f : ℝ≥0 → ℝ := fun s => ((min s cap : ℝ≥0) : ℝ)
    have cf : Continuous f := continuous_subtype_val.comp (continuous_id.min continuous_const)
    have hf : MapsTo f (Ici u) (Ici (f u)) := by
      intro s hs
      exact_mod_cast min_le_min_right cap hs
    have hc := ((@IsPoissonProcess.cadlag Ω mΩ P N rate hN ω).1 (f u) (NNReal.coe_nonneg _))
    exact (hc.comp cf.continuousWithinAt) hf
  have h := @AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation Ω G
    (fun u ω => N ω (min u cap : ℝ≥0)) (fun u => hm _ (min_le_right _ _)) hRight
  letI : MeasurableSpace Ω := G
  exact h.comp (ht.real_toNNReal.prodMk measurable_id)

private theorem limitedCounts_meas {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0)
    {z : Ω → ClockSnapshot k} (hz : Measurable[primitiveCutInfo M n d p q] z)
    {t : Ω → ℝ} (ht : Measurable[primitiveCutInfo M n d p q] t) (i : Fin k) :
    Measurable[primitiveCutInfo M n d p q] (fun ω => limitedCounts M n F d p q ω (z ω) (t ω) i) := by
  have hS := capped_poisson_eval_meas (M.S_poisson n i) (primitiveCutInfo M n d p q) (p i)
    (fun u hu => measurable_iff_comap_le.2
      ((le_iSup_of_le i (le_iSup_of_le u
        (le_iSup (fun _ : u ≤ p i => MeasurableSpace.comap (fun ω => M.S n i ω u) inferInstance) hu))).trans
        (le_sup_right.trans le_sup_left))) (@frozenS_meas Ω (primitiveCutInfo M n d p q) k F z hz t ht i)
  have hR := capped_poisson_eval_meas (M.R_poisson n i) (primitiveCutInfo M n d p q) (q i)
    (fun u hu => measurable_iff_comap_le.2
      ((le_iSup_of_le i (le_iSup_of_le u
        (le_iSup (fun _ : u ≤ q i => MeasurableSpace.comap (fun ω => M.R n i ω u) inferInstance) hu))).trans
        le_sup_right))
      (@frozenR_meas Ω (primitiveCutInfo M n d p q) k F z hz t ht i)
  exact (cut_arrival_meas M n d p q ht i).prodMk (hS.prodMk hR)

private theorem limitedTotal_meas {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0)
    {z : Ω → ClockSnapshot k} (hz : Measurable[primitiveCutInfo M n d p q] z)
    {t : Ω → ℝ} (ht : Measurable[primitiveCutInfo M n d p q] t) :
    Measurable[primitiveCutInfo M n d p q] (fun ω => limitedTotal M n F d p q ω (z ω) (t ω)) :=
  Finset.measurable_sum _ (fun i _ => by
    have hm := limitedCounts_meas M n F d p q hz ht i
    exact (hm.fst.add hm.snd.fst).add hm.snd.snd)

set_option maxHeartbeats 800000 in
private theorem limitedAdvance_meas {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (T : ℝ)
    {z : Ω → ClockSnapshot k} (hz : Measurable[primitiveCutInfo M n d p q] z) :
    Measurable[primitiveCutInfo M n d p q] (fun ω => limitedAdvance M n X0 F d p q T ω (z ω)) := by
  classical
  let t ω := nextEvent (z ω).1 T (limitedTotal M n F d p q ω (z ω))
  let v ω := proposal M n X0 F d p q T ω (z ω)
  have htotal := @limitedTotal_meas Ω mΩ k M n F d p q z hz
  have hcount := @limitedCounts_meas Ω mΩ k M n F d p q z hz
  let G := @primitiveCutInfo Ω mΩ k M n d p q
  letI : MeasurableSpace Ω := G
  have ht : Measurable[G] t := by
    apply Measurable.iInf
    intro r
    apply Measurable.ite _ measurable_const measurable_const
    by_cases hr : (r : ℝ) < T
    · simpa only [hr, true_and, Set.ofPred_and] using
        (measurableSet_lt hz.fst (measurable_const (a := (r : ℝ)))).inter
          (measurableSet_lt (htotal hz.fst) (htotal (measurable_const (a := (r : ℝ)))))
    · simp [hr]
  have hv : Measurable[G] v := by
    exact ht.prodMk ((measurable_pi_lambda _ (fun i => by
      have hm := hcount ht i
      exact ((((measurable_const (a := (X0 i : ℝ))).add hm.fst).sub hm.snd.fst).sub hm.snd.snd).nat_floor)).prodMk
      ((measurable_pi_lambda _ (@frozenS_meas Ω G k F z hz t ht)).prodMk
        (measurable_pi_lambda _ (@frozenR_meas Ω G k F z hz t ht))))
  have hB : MeasurableSet[G] {ω | insideBox p q (v ω)} := by
    simp only [insideBox, ofPred_forall, ofPred_and]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_le ((measurable_pi_apply i).comp hv.snd.snd.fst) measurable_const).inter
        (measurableSet_le ((measurable_pi_apply i).comp hv.snd.snd.snd) measurable_const)
  exact Measurable.ite hB hv hz
private def covered {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (T : ℝ) : Set Ω :=
  {ω | ∀ i, T ≤ M.arrivalEpoch n i ω (d i)}

private def cutRectangle {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (X : Ω → ℝ → Fin k → ℕ) (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (T : ℝ) : Set Ω :=
  {ω | ω ∈ covered M n d T ∧ insideBox p q (actualSnap F X ω T)}

private noncomputable def limitedRun {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (T : ℝ) : ℕ → Ω → ClockSnapshot k :=
  Nat.rec (fun _ => ((0 : ℝ), X0, (fun _ => 0), (fun _ => 0)))
    (fun _ old ω => limitedAdvance M n X0 F d p q T ω (old ω))

private theorem limit_run_meas {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (T : ℝ) (m : ℕ) :
    Measurable[primitiveCutInfo M n d p q] (limitedRun M n X0 F d p q T m) := by
  induction m with
  | zero =>
    change Measurable[primitiveCutInfo M n d p q] (fun _ : Ω =>
      ((0 : ℝ), X0, (fun _ => (0 : ℝ)), fun _ => (0 : ℝ)))
    exact measurable_const
  | succ m hm => exact limitedAdvance_meas M n X0 F d p q T hm

private theorem limit_run_correct {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ v i, F v i ≤ v i) (X : Ω → ℝ → Fin k → ℕ)
    (hC : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)))
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (ω : Ω) (hω : ω ∈ covered M n d T) :
    let Z := limitedRun M n X0 F d p q T
    (∀ m, (Z m ω).1 ∈ Icc 0 T ∧ insideBox p q (Z m ω) ∧ Z m ω = actualSnap F X ω (Z m ω).1) ∧
      (insideBox p q (actualSnap F X ω T) ↔ ∃ m, (Z m ω).1 = T) := by
  classical
  let Z := limitedRun M n X0 F d p q T
  change (∀ m, (Z m ω).1 ∈ Icc 0 T ∧ insideBox p q (Z m ω) ∧
    Z m ω = actualSnap F X ω (Z m ω).1) ∧ _
  have hA0 (i : Fin k) : M.A n i ω 0 = 0 := by
    have he : M.arrivalEpoch n i ω 0 = 0 := by simp [SystemSequence.arrivalEpoch, partialSum]
    have h1 := (epoch_strict M n i ω) (Nat.zero_lt_succ 0)
    rw [he] at h1
    unfold SystemSequence.A
    simp only [renewal_eq_of_bracket (epoch_strict M n i ω).monotone he.le h1, ENat.toNat_zero, Nat.cast_zero]
  have hXzero : X ω 0 = X0 := by
    funext i
    apply Nat.cast_injective (R := ℝ)
    have he := hC.eq7 ω 0 i le_rfl
    simpa only [hA0, queueTime, busyTime, intervalIntegral.integral_same,
      (M.S_poisson n i).zero ω, (M.R_poisson n i).zero ω, add_zero, sub_zero] using he
  have hstep (m : ℕ) (hm : (Z m ω).1 ∈ Icc 0 T) (hb : insideBox p q (Z m ω))
      (he : Z m ω = actualSnap F X ω (Z m ω).1) :
      (Z (m+1) ω).1 ∈ Icc (Z m ω).1 T ∧ insideBox p q (Z (m+1) ω) ∧
      Z (m+1) ω = actualSnap F X ω (Z (m+1) ω).1 ∧
      (insideBox p q (actualSnap F X ω T) →
        Z (m+1) ω = advance M n X0 F T ω (actualSnap F X ω (Z m ω).1)) := by
    have h := limitedAdvance_actual_box M n X0 F hF X hC d p q ω (Z m ω).1 T
      hm.1 hm.2 hω (he ▸ hb)
    dsimp only at h
    have hn : Z (m+1) ω = limitedAdvance M n X0 F d p q T ω (actualSnap F X ω (Z m ω).1) :=
      congrArg (limitedAdvance M n X0 F d p q T ω) he
    rw [hn]
    exact h
  have hsim (m : ℕ) : (Z m ω).1 ∈ Icc 0 T ∧ insideBox p q (Z m ω) ∧
      Z m ω = actualSnap F X ω (Z m ω).1 := by
    induction m with
    | zero =>
      refine ⟨⟨le_rfl, hT⟩, (fun i => ⟨NNReal.coe_nonneg _, NNReal.coe_nonneg _⟩), ?_⟩
      simp [Z, limitedRun, actualSnap, hXzero, queueTime, busyTime]
    | succ m hm =>
      have h := hstep m hm.1 hm.2.1 hm.2.2
      exact ⟨⟨hm.1.1.trans h.1.1, h.1.2⟩, h.2.1, h.2.2.1⟩
  refine ⟨hsim, ?_⟩
  change insideBox p q (actualSnap F X ω T) ↔ ∃ m, (Z m ω).1 = T
  constructor
  · intro hc
    by_contra! hne
    let f (m : ℕ) : ℕ := ⌊actualTotal M n F X ω (Z m ω).1⌋₊
    have hf (m : ℕ) : actualTotal M n F X ω (Z m ω).1 = f m := by
      obtain ⟨p, hp⟩ := frozenTotal_nat M n F ω (actualSnap F X ω (Z m ω).1) (Z m ω).1
      change actualTotal M n F X ω (Z m ω).1 = (p : ℝ) at hp
      simp [f, hp]
    have hstrict : StrictMono f := by
      apply strictMono_nat_of_lt_succ
      intro m
      have hm := hsim m
      have hM := hsim (m + 1)
      have hlt : (Z (m + 1) ω).1 < T := lt_of_le_of_ne hM.1.2 (hne (m + 1))
      have h := advance_actual M n X0 F hF X hC ω (Z m ω).1 T hm.1.1 hm.1.2
      have hnext := (hstep m hm.1 hm.2.1 hm.2.2).2.2.2 hc
      rw [hnext] at hlt
      have hh := h.2.2 hlt
      rw [← hnext, hf m, hf (m + 1)] at hh
      exact_mod_cast hh
    have hub (m : ℕ) : f m ≤ ⌊actualTotal M n F X ω T⌋₊ :=
      Nat.floor_mono (actualTotal_mono M n X0 F X hC ω (hsim m).1.1 hT (hsim m).1.2)
    let m := ⌊actualTotal M n F X ω T⌋₊ + 1
    have hlow : m ≤ f m := hstrict.id_le m
    have hhi := hub m
    dsimp [m] at *
    omega
  · rintro ⟨m, hm⟩
    have he := (hsim m).2.2
    rw [hm] at he
    exact he ▸ (hsim m).2.1

private theorem cut_box_of_le {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (X : Ω → ℝ → Fin k → ℕ)
    (hC : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)))
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) {s T : ℝ} (hs : s ∈ Icc 0 T)
    {ω : Ω} (h : ω ∈ cutRectangle M n F X d p q T) :
    ω ∈ cutRectangle M n F X d p q s := by
  refine ⟨fun i => hs.2.trans (h.1 i), fun i => ?_⟩
  have hS := clock_monotone (fun t ht => (hC.integrable ω i t ht).1)
    (fun t ht => hC.psi_nonneg ω t i ht) hs.1 (hs.1.trans hs.2) hs.2
  have hR := clock_monotone (fun t ht => (hC.integrable ω i t ht).2)
    (fun t ht => hC.phi_nonneg ω t i ht) hs.1 (hs.1.trans hs.2) hs.2
  exact ⟨hS.trans (h.2 i).1, hR.trans (h.2 i).2⟩

private theorem cut_rectangle_meas {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ v i, F v i ≤ v i) (X : Ω → ℝ → Fin k → ℕ)
    (hC : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)))
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (T : ℝ) (hT : 0 ≤ T) :
    MeasurableSet[primitiveCutInfo M n d p q] (cutRectangle M n F X d p q T) := by
  let Z := limitedRun M n X0 F d p q T
  let D := cutRectangle M n F X d p q T
  let C := covered M n d T
  have hD : D = C ∩ ⋃ m, {ω | (Z m ω).1 = T} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
    change ω ∈ C ∧ insideBox p q (actualSnap F X ω T) ↔ ω ∈ C ∧ ∃ m, (Z m ω).1 = T
    exact and_congr_right (fun hω => (limit_run_correct M n X0 F hF X hC d p q T hT ω hω).2)
  have hM := @limit_run_meas Ω mΩ k M n X0 F d p q T
  have hE (i : Fin k) := @cut_epoch_meas Ω mΩ k M n d p q i (d i) le_rfl
  let G := @primitiveCutInfo Ω mΩ k M n d p q
  letI : MeasurableSpace Ω := G
  change MeasurableSet D
  rw [hD]
  refine MeasurableSet.inter ?_ (MeasurableSet.iUnion (fun m => measurableSet_eq_fun (hM m).fst measurable_const))
  change MeasurableSet {ω | ∀ i : Fin k, T ≤ @SystemSequence.arrivalEpoch Ω mΩ k M n i ω (d i)}
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (hE i))

set_option maxHeartbeats 1500000 in
private theorem cut_past_restrict {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ v i, F v i ≤ v i) (X : Ω → ℝ → Fin k → ℕ)
    (hC : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)))
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (T : ℝ) :
    let D := cutRectangle M n F X d p q T
    let Xr : Ω → ℝ → Fin k → ℝ := fun ω t i => (X ω t i : ℝ)
    let Ψ : Ω → ℝ → Fin k → ℝ := fun ω t i => (F (X ω t) i : ℝ)
    (M.pastInfo n Xr Ψ T).comap (Subtype.val : D → Ω) ≤
      (primitiveCutInfo M n d p q).comap (Subtype.val : D → Ω) := by
  classical
  let D := cutRectangle M n F X d p q T
  let Xr : Ω → ℝ → Fin k → ℝ := fun ω t i => (X ω t i : ℝ)
  let Ψ : Ω → ℝ → Fin k → ℝ := fun ω t i => (F (X ω t) i : ℝ)
  let Gv := (primitiveCutInfo M n d p q).comap (Subtype.val : D → Ω)
  change (M.pastInfo n Xr Ψ T).comap (Subtype.val : D → Ω) ≤ Gv
  unfold SystemSequence.pastInfo
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_sup, MeasurableSpace.comap_comp]
  refine iSup_le (fun i => iSup_le (fun s => iSup_le (fun (hs : s ∈ Icc 0 T) => ?_)))
  let Z (m : ℕ) (ω : D) := limitedRun M n X0 F d p q s m ω.val
  have hM (m : ℕ) : Measurable[Gv] (Z m) := by
    exact (limit_run_meas M n X0 F d p q s m).comp
      (@measurable_subtype_coe Ω (primitiveCutInfo M n d p q) _)
  have hrect (ω : D) := cut_box_of_le M n X0 F X hC d p q hs ω.property
  have hr (ω : D) := limit_run_correct M n X0 F hF X hC d p q s hs.1 ω.val (hrect ω).1
  have hHit (ω : D) : ∃ m, (Z m ω).1 = s := (hr ω).2.mp (hrect ω).2
  let L (ω : D) := Z (Nat.find (hHit ω)) ω
  have hL (ω : D) : L ω = actualSnap F X ω.val s := by
    have he := ((hr ω).1 (Nat.find (hHit ω))).2.2
    change L ω = actualSnap F X ω.val (L ω).1 at he
    rw [show (L ω).1 = s from Nat.find_spec (hHit ω)] at he
    exact he
  let C (ω : D) := limitedCounts M n F d p q ω.val (L ω) s i
  have hCeq (ω : D) : C ω = (M.A n i ω.val s, M.S n i ω.val (busyTime Ψ ω.val i s),
      M.R n i ω.val (queueTime Xr Ψ ω.val i s)) := by
    have hsS (j : Fin k) : 0 ≤ busyTime Ψ ω.val j s :=
      intervalIntegral.integral_nonneg hs.1 (fun t ht => hC.psi_nonneg ω.val t j ht.1)
    have hsR (j : Fin k) : 0 ≤ queueTime Xr Ψ ω.val j s :=
      intervalIntegral.integral_nonneg hs.1 (fun t ht => hC.phi_nonneg ω.val t j ht.1)
    dsimp [C]
    rw [hL, limitedCounts_eq M n F d p q ω.val _ s hs.1 (hrect ω).1]
    · simp [frozenCounts, frozenS, frozenR, actualSnap, Xr, Ψ,
        Real.coe_toNNReal _ hs.1, Real.coe_toNNReal _ (hsS i), Real.coe_toNNReal _ (hsR i)]
    · intro j
      simpa [frozenS, actualSnap] using ((hrect ω).2 j).1
    · intro j
      simpa [frozenR, actualSnap] using ((hrect ω).2 j).2
  have hLmeas : Measurable[Gv] L := by
    letI : MeasurableSpace D := Gv
    exact Measurable.find hM (fun m => measurableSet_eq_fun (hM m).fst measurable_const) hHit
  have hCmeas : Measurable[Gv] C := by
    -- Prove the capped evaluations with the same fixed-time section argument on the restricted domain.
    let G := @primitiveCutInfo Ω mΩ k M n d p q
    have hSM (u : ℝ≥0) (hu : u ≤ p i) : Measurable[G] (fun ω => @SystemSequence.S Ω mΩ k M n i ω u) := by
      apply measurable_iff_comap_le.2
      exact (le_iSup_of_le i (le_iSup_of_le u
        (le_iSup (fun _ : u ≤ p i => MeasurableSpace.comap
          (fun ω => @SystemSequence.S Ω mΩ k M n i ω u) inferInstance) hu))).trans
          (le_sup_right.trans le_sup_left)
    have hRM (u : ℝ≥0) (hu : u ≤ q i) : Measurable[G] (fun ω => @SystemSequence.R Ω mΩ k M n i ω u) := by
      apply measurable_iff_comap_le.2
      exact (le_iSup_of_le i (le_iSup_of_le u
        (le_iSup (fun _ : u ≤ q i => MeasurableSpace.comap
          (fun ω => @SystemSequence.R Ω mΩ k M n i ω u) inferInstance) hu))).trans le_sup_right
    have hconst : Measurable[G] (fun _ : Ω => s) := by exact measurable_const
    have hN := @cut_arrival_meas Ω mΩ k M n d p q (fun _ => s) hconst i
    let v : D → Ω := Subtype.val
    have hv : Measurable[Gv] v := @measurable_subtype_coe Ω G _
    have hRight (N : Ω → ℝ → ℝ) (hN : ∀ ω, IsCadlag (N ω)) (cap : ℝ≥0) (ω : D) (u : ℝ≥0) :
        ContinuousWithinAt (fun w : ℝ≥0 => N ω.val ((min w cap : ℝ≥0) : ℝ)) (Ici u) u := by
      let f : ℝ≥0 → ℝ := fun w => ((min w cap : ℝ≥0) : ℝ)
      have cf : Continuous f := continuous_subtype_val.comp (continuous_id.min continuous_const)
      have hf : MapsTo f (Ici u) (Ici (f u)) := by
        intro w hw
        exact_mod_cast min_le_min_right cap hw
      exact (((hN ω.val).1 (f u) (NNReal.coe_nonneg _)).comp cf.continuousWithinAt) hf
    have hSjoint := @AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation D Gv
      (fun u ω => @SystemSequence.S Ω mΩ k M n i ω.val (min u (p i) : ℝ≥0))
      (fun u => (hSM _ (min_le_right _ _)).comp hv)
      (hRight (@SystemSequence.S Ω mΩ k M n i) (@IsPoissonProcess.cadlag Ω mΩ _ _ _
        (@SystemSequence.S_poisson Ω mΩ k M n i)) (p i))
    have hRjoint := @AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation D Gv
      (fun u ω => @SystemSequence.R Ω mΩ k M n i ω.val (min u (q i) : ℝ≥0))
      (fun u => (hRM _ (min_le_right _ _)).comp hv)
      (hRight (@SystemSequence.R Ω mΩ k M n i) (@IsPoissonProcess.cadlag Ω mΩ _ _ _
        (@SystemSequence.R_poisson Ω mΩ k M n i)) (q i))
    letI : MeasurableSpace D := Gv
    exact (hN.comp hv).prodMk
      ((hSjoint.comp ((frozenS_meas F hLmeas measurable_const i).real_toNNReal.prodMk measurable_id)).prodMk
        (hRjoint.comp ((frozenR_meas F hLmeas measurable_const i).real_toNNReal.prodMk measurable_id)))
  have hObs : C = (fun ω : D => (M.A n i ω.val s, M.S n i ω.val (busyTime Ψ ω.val i s),
      M.R n i ω.val (queueTime Xr Ψ ω.val i s))) := funext hCeq
  rw [hObs] at hCmeas
  letI : MeasurableSpace D := Gv
  have hstate : Measurable (fun ω : D => X ω.val s) := by
    have hh : (fun ω : D => (L ω).2.1) = (fun ω : D => X ω.val s) := by
      funext ω
      exact congrArg (fun z : ClockSnapshot k => z.2.1) (hL ω)
    exact hh ▸ hLmeas.snd.fst
  have hXm : Measurable (fun ω : D => Xr ω.val s i) :=
    (measurable_of_countable (fun v : Fin k → ℕ => (v i : ℝ))).comp hstate
  have hΨm : Measurable (fun ω : D => Ψ ω.val s i) :=
    (measurable_of_countable (fun v : Fin k → ℕ => (F v i : ℝ))).comp hstate
  exact sup_le (sup_le (sup_le (sup_le (sup_le (measurable_iff_comap_le.mp hCmeas.fst)
    (measurable_iff_comap_le.mp hCmeas.snd.fst)) (measurable_iff_comap_le.mp hCmeas.snd.snd))
    (measurable_iff_comap_le.mp (hXm.sub hΨm))) (measurable_iff_comap_le.mp hΨm))
    (measurable_iff_comap_le.mp hXm)

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ v i, F v i ≤ v i) (X : Ω → ℝ → Fin k → ℕ)
    (hC : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)))
    (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) (T : ℝ) (hT : 0 ≤ T) (B : Set Ω) :
    let Xr : Ω → ℝ → Fin k → ℝ := fun ω t i => (X ω t i : ℝ)
    let Ψ : Ω → ℝ → Fin k → ℝ := fun ω t i => (F (X ω t) i : ℝ)
    let G : MeasurableSpace Ω :=
      (⨆ (i : Fin k) (j : ℕ) (_ : j < d i), MeasurableSpace.comap (M.U i (j+1)) inferInstance) ⊔
        (⨆ (i : Fin k) (u : ℝ≥0) (_ : u ≤ p i), MeasurableSpace.comap (fun ω => M.S n i ω u) inferInstance) ⊔
        (⨆ (i : Fin k) (u : ℝ≥0) (_ : u ≤ q i), MeasurableSpace.comap (fun ω => M.R n i ω u) inferInstance)
    MeasurableSet[@SystemSequence.pastInfo Ω mΩ k M n Xr Ψ T] B →
      MeasurableSet[G] (B ∩ {ω | (∀ i, T ≤ @SystemSequence.arrivalEpoch Ω mΩ k M n i ω (d i)) ∧
        (∀ i, busyTime Ψ ω i T ≤ p i ∧ queueTime Xr Ψ ω i T ≤ q i)}) := by
  let Xr : Ω → ℝ → Fin k → ℝ := fun ω t i => (X ω t i : ℝ)
  let Ψ : Ω → ℝ → Fin k → ℝ := fun ω t i => (F (X ω t) i : ℝ)
  let D := cutRectangle M n F X d p q T
  let v : D → Ω := Subtype.val
  change MeasurableSet[M.pastInfo n Xr Ψ T] B →
    MeasurableSet[primitiveCutInfo M n d p q] (B ∩ D)
  intro hB
  have hle := cut_past_restrict M n X0 F hF X hC d p q T
  have hPre : MeasurableSet[(primitiveCutInfo M n d p q).comap v] (v ⁻¹' B) := by
    apply hle
    exact ⟨B, hB, rfl⟩
  obtain ⟨E, hE, hEq⟩ := hPre
  have hD := cut_rectangle_meas M n X0 F hF X hC d p q T hT
  have he : B ∩ D = E ∩ D := by
    ext ω
    constructor
    · rintro ⟨hb, hr⟩
      have ha : (⟨ω, hr⟩ : D) ∈ v ⁻¹' B := hb
      rw [← hEq] at ha
      exact ⟨ha, hr⟩
    · rintro ⟨hb, hr⟩
      have ha : (⟨ω, hr⟩ : D) ∈ v ⁻¹' E := hb
      rw [hEq] at ha
      exact ⟨ha, hr⟩
  rw [he]
  exact hE.inter hD

