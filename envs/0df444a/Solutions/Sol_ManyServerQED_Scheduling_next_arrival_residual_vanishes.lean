-- Prove2me | solution 1 for ManyServerQED.Scheduling.next_arrival_residual_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:06:59.85508+00:00
-- url     : https://prove2.me/submissions/99acfc5c-22af-44af-a133-37199d932c3b

import Theorems.Thm_ManyServerQED_Scheduling_lemma_2

open MeasureTheory ProbabilityTheory Filter Topology Set
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


private theorem next_epoch_upper {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (t : ℝ) (j : ℕ)
    (h : t ≤ M.arrivalEpoch n i ω (j+1)) :
    M.nextArrival n i ω t ≤ M.arrivalEpoch n i ω (j+1) := by
  unfold SystemSequence.nextArrival
  exact csInf_le ⟨t, fun _ hu => hu.1⟩ ⟨h, j+1, by omega,rfl⟩

set_option maxHeartbeats 1000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k)
    (mL mU : ℝ) (hA3 : M.Assumption3 mL mU) (i : Fin k)
    (t : ℝ) (ht : 0 ≤ t) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => M.P {ω | ε ≤ M.nextArrival n i ω t - t}) atTop (𝓝 0) := by
  let : IsProbabilityMeasure M.P := M.isProb
  let T := t+ε/2
  have hT : 0 ≤ T := by dsimp [T]; linarith
  have htT : t ≤ T := by dsimp [T]; linarith
  have hA (n : ℕ) (ω : Ω) (hbad : ε ≤ M.nextArrival n i ω t-t) :
      M.A n i ω T = M.A n i ω t := by
    obtain ⟨j,hj,hj'⟩ := path_above_bound M n i ω t ht
    have hu := next_epoch_upper M n i ω t j hj'.le
    have hT' : T < M.arrivalEpoch n i ω (j+1) := by
      dsimp [T]
      linarith
    have hmono := (arrival_epoch_strict M n i ω).monotone
    simp [SystemSequence.A, renewal_eq_of_bracket hmono hj hj',
      renewal_eq_of_bracket hmono (hj.trans htT) hT']
  let b := M.lam i * ε / 8
  have hb : 0 < b := by dsimp [b]; positivity [M.lam_pos i]
  have hRate : ∀ᶠ n in atTop, M.lam i/2 ≤ M.lamN n i / (n:ℝ) := by
    have hhalf : M.lam i/2 < M.lam i := by linarith [M.lam_pos i]
    exact ((tendsto_order.1 (M.lam_lim i)).1 _ hhalf).mono (fun _ h => h.le)
  obtain ⟨C,hC⟩ := lemma_2 M mL mU hA3
  let K := ENNReal.ofReal (C*(1+T^(mU/2)))
  have hp : 0 < mU := by linarith [hA3.1]
  let R (n : ℕ) := ENNReal.ofReal (b*Real.sqrt n)^mU
  have hR : Tendsto R atTop (𝓝 ⊤) := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => b*Real.sqrt n) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos hb).2 h1
    have h3 : Tendsto (fun n : ℕ => ENNReal.ofReal (b*Real.sqrt n)) atTop (𝓝 ⊤) :=
      ENNReal.tendsto_ofReal_atTop.comp h2
    have h4 := (ENNReal.continuous_rpow_const (y := mU)).continuousAt.tendsto.comp h3
    simpa only [R, Function.comp_def, ENNReal.top_rpow_of_pos hp] using h4
  have hlim : Tendsto (fun n => 2*K*(R n)⁻¹) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => (R n)⁻¹) atTop (𝓝 (0:ℝ≥0∞)) := by
      have h := tendsto_inv_iff.2 hR
      simpa only [ENNReal.inv_top] using h
    have hK : (2:ℝ≥0∞)*K ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul h0 (Or.inr hK)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => zero_le)) ?_
  filter_upwards [hRate,eventually_ge_atTop (1:ℕ)] with n hnRate hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hsqr : Real.sqrt (n:ℝ)^2 = n := Real.sq_sqrt hn0.le
  let Z (s : ℝ) (ω : Ω) := |M.Ahat n ω s i|
  let E (s : ℝ) := {ω | b*Real.sqrt n ≤ Z s ω}
  have hE (s : ℝ) (hs : 0 ≤ s) : MeasurableSet (E s) := by
    have hMeas := (((arrival_measurable_of_nonnegative_time M n i s hs).sub_const
      (M.lamN n i*s)).div_const (Real.sqrt n)).abs
    exact measurableSet_le measurable_const hMeas
  have hsub : {ω | ε ≤ M.nextArrival n i ω t-t} ⊆ E t ∪ E T := by
    intro ω hω
    by_contra! hno
    have hT0 : Z T ω < b*Real.sqrt n := not_le.mp (fun h => hno (Or.inr h))
    have ht0 : Z t ω < b*Real.sqrt n := not_le.mp (fun h => hno (Or.inl h))
    have hEq := hA n ω hω
    have he : M.Ahat n ω t i - M.Ahat n ω T i = (M.lamN n i * (T-t)) / Real.sqrt n := by
      simp only [SystemSequence.Ahat, hEq, ← sub_div]
      ring
    have hlarge : (M.lamN n i * (T-t)) / Real.sqrt n ≥ 2*b*Real.sqrt n := by
      apply (le_div_iff₀ hsq).2
      have hl := (le_div_iff₀ hn0).1 hnRate
      have hTeq : T-t=ε/2 := by dsimp [T]; ring
      rw [hTeq, mul_assoc, ← pow_two, hsqr]
      unfold b
      nlinarith [mul_le_mul_of_nonneg_right hl hε.le]
    have hsmall : M.Ahat n ω t i - M.Ahat n ω T i < 2*b*Real.sqrt n := by
      have h1 := (le_abs_self (M.Ahat n ω t i)).trans_lt ht0
      have h2 := (neg_le_abs (M.Ahat n ω T i)).trans_lt hT0
      linarith
    exact not_lt_of_ge (he.symm ▸ hlarge) hsmall
  have hBound (s : ℝ) (hs : s ∈ Icc 0 T) : M.P (E s) ≤ K*(R n)⁻¹ := by
    have hm : R n * M.P (E s) ≤ ∫⁻ ω, supDist (M.Ahat n ω) (fun _ => 0) T ^ mU ∂M.P := by
      rw [← lintegral_indicator_const (hE s hs.1)]
      apply lintegral_mono
      intro ω
      by_cases he : ω ∈ E s
      · rw [indicator_of_mem he]
        apply ENNReal.rpow_le_rpow _ hp.le
        apply le_iSup₂_of_le s hs
        simp only [Pi.zero_apply, sub_zero]
        exact ENNReal.ofReal_le_ofReal ((show b * Real.sqrt n ≤ |M.Ahat n ω s i| from he).trans
          (Finset.single_le_sum (f := fun j => |M.Ahat n ω s j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
      · rw [indicator_of_notMem he]
        exact zero_le
    have hm' := hm.trans (hC n hn T hT)
    have hn0' : R n ≠ 0 :=
      (ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.2 (mul_pos hb hsq)) hp.le).ne'
    have hnT : R n ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
    have hr := mul_le_mul_right hm' (R n)⁻¹
    rw [← mul_assoc, ENNReal.inv_mul_cancel hn0' hnT, one_mul] at hr
    simpa [K, mul_comm] using hr
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  exact (add_le_add (hBound t ⟨ht,htT⟩) (hBound T ⟨hT,le_rfl⟩)).trans_eq (by ring)
