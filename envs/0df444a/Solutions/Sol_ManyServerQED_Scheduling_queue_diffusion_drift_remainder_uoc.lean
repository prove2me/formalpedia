-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_diffusion_drift_remainder_uoc
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:39:12.670894+00:00
-- url     : https://prove2.me/submissions/5bfe2296-ed33-4a6f-8782-0379e80e5630

import Theorems.Thm_ManyServerQED_Scheduling_controlled_compact_containment

open MeasureTheory Set Filter Topology
open scoped ENNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private noncomputable def inputRate {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) : ℝ :=
  (M.lamN n i - M.rho i * M.muN n i * n) / Real.sqrt n

private theorem inputRate_tendsto {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (i : Fin k) :
    Tendsto (fun n => inputRate M n i) atTop (𝓝 (M.ell i)) := by
  have hlim := (M.lamHat_lim i).sub (tendsto_const_nhds.mul (M.muHat_lim i) :
    Tendsto (fun n : ℕ => M.rho i * (Real.sqrt n * (M.muN n i - M.mu i))) atTop
      (𝓝 (M.rho i * M.muHat i)))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn'
  have hmul : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
  have hρ : M.rho i * M.mu i = M.lam i := div_mul_cancel₀ _ (M.mu_pos i).ne'
  unfold inputRate
  symm
  apply (div_eq_iff hs.ne').2
  symm
  calc
    (Real.sqrt (n : ℝ) * (M.lamN n i / n - M.lam i) -
        M.rho i * (Real.sqrt n * (M.muN n i - M.mu i))) * Real.sqrt n =
      (Real.sqrt n * Real.sqrt n) *
        (M.lamN n i / n - M.lam i - M.rho i * (M.muN n i - M.mu i)) := by ring
    _ = _ := by
      rw [hmul]
      calc
        (n : ℝ) * (M.lamN n i / n - M.lam i - M.rho i * (M.muN n i - M.mu i)) =
            M.lamN n i - (n : ℝ) * M.lam i -
              (n : ℝ) * M.rho i * M.muN n i + (n : ℝ) * (M.rho i * M.mu i) := by
          rw [mul_sub, mul_sub, mul_div_cancel₀ _ hn'.ne']
          ring
        _ = _ := by rw [hρ]; ring

private theorem diffusion_drift_equation {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (hn : 1 ≤ n)
    (X0 : Fin k → ℕ) (X Ψ : Ω → ℝ → Fin k → ℝ)
    (hC : M.IsControlled n X0 X Ψ) (hWork : IsWorkConserving n X Ψ)
    (u0 : Fin k → ℝ) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (i : Fin k) :
    M.Xhat n X ω t i = M.Xhat0 n X0 i +
      (M.Ahat n ω t i - M.Rhat n ω (queueTime X Ψ ω i t / (n : ℝ)) i -
      M.Shat n ω (busyTime Ψ ω i t / (n : ℝ)) i) +
      ∫ s in (0 : ℝ)..t,
        drift M.diffData (M.Xhat n X ω s) (uProc n u0 X Ψ ω s) i +
        (inputRate M n i - M.ell i) +
          ((M.muN n i - M.thetaN n i) - (M.mu i - M.theta i)) * Phihat n X Ψ ω s i -
          (M.muN n i - M.mu i) * M.Xhat n X ω s i := by
  let W (ω : Ω) (t : ℝ) (i : Fin k) :=
    M.Xhat0 n X0 i + M.Ahat n ω t i -
      M.Rhat n ω (queueTime X Ψ ω i t / n) i -
      M.Shat n ω (busyTime Ψ ω i t / n) i + inputRate M n i * t
  let xx (s : ℝ) := M.Xhat n X ω s
  let pp (s : ℝ) := M.Psihat n Ψ ω s
  let qq (s : ℝ) := Phihat n X Ψ ω s
  let r : ℝ := Real.sqrt n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.2 hn'
  have hpp (s : ℝ) (i : Fin k) : pp s i = xx s i - qq s i := by
    change (Ψ ω s i - M.rho i * n) / r = (X ω s i - M.rho i * n) / r - (X ω s i - Ψ ω s i) / r
    ring
  have hint (t : ℝ) (ht : 0 ≤ t) (i : Fin k) :
      IntervalIntegrable (fun s => xx s i) volume 0 t ∧
      IntervalIntegrable (fun s => pp s i) volume 0 t ∧
      IntervalIntegrable (fun s => qq s i) volume 0 t := by
    have h := hC.integrable ω i t ht
    have hp' : IntervalIntegrable (fun s => pp s i) volume 0 t :=
      (h.1.sub (intervalIntegrable_const (c := M.rho i * n))).div_const r
    have hq' : IntervalIntegrable (fun s => qq s i) volume 0 t := h.2.div_const r
    refine ⟨?_, hp', hq'⟩
    have he : (fun s => xx s i) = (fun s => pp s i + qq s i) := by
      funext s
      rw [hpp, sub_add_cancel]
    rw [he]
    exact hp'.add hq'
  have hqn (s : ℝ) (hs : 0 ≤ s) (i : Fin k) : 0 ≤ qq s i :=
    div_nonneg (hC.phi_nonneg ω s i hs) hr.le
  have hq (t : ℝ) (ht : 0 ≤ t) : (∑ i, qq t i) = max (∑ i, xx t i) 0 := by
    have hs : (∑ i, xx t i) = ((∑ i, X ω t i) - n) / r := by
      simp only [xx, SystemSequence.Xhat, ← Finset.sum_div, Finset.sum_sub_distrib,
        ← Finset.sum_mul, show (∑ i, M.rho i) = 1 from M.sum_rho, one_mul, r]
    simp only [qq, Phihat, ← Finset.sum_div, ← hWork ω t ht]
    rw [← max_div_div_right (show 0 ≤ Real.sqrt (n : ℝ) from hr.le), zero_div, hs]
  have hbalance (t : ℝ) (ht : 0 ≤ t) (i : Fin k) :
      xx t i = W ω t i -
        M.muN n i * (∫ s in (0 : ℝ)..t, pp s i) -
        M.thetaN n i * (∫ s in (0 : ℝ)..t, qq s i) := by
    have hIntP : (∫ s in (0 : ℝ)..t, pp s i) = (busyTime Ψ ω i t - t * (M.rho i * n)) / r := by
      change (∫ s in (0 : ℝ)..t, (Ψ ω s i - M.rho i * n) / r) = _
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_sub (hC.integrable ω i t ht).1 intervalIntegrable_const]
      simp only [busyTime, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have hIntQ : (∫ s in (0 : ℝ)..t, qq s i) = queueTime X Ψ ω i t / r :=
      intervalIntegral.integral_div _ _
    rw [hIntP, hIntQ]
    simp only [xx, W, SystemSequence.Xhat, SystemSequence.Xhat0, SystemSequence.Ahat,
      SystemSequence.Rhat, SystemSequence.Shat]
    rw [hC.eq7 ω t i ht]
    dsimp [r]
    have div_scale (s : ℝ) : (n : ℝ) * (s / n) = s := mul_div_cancel₀ _ hn'.ne'
    have rate_scale (b s : ℝ) : (n : ℝ) * b * (s / n) = b * s := by
      rw [mul_comm (n : ℝ) b, mul_assoc, div_scale]
    rw [div_scale, div_scale, rate_scale, rate_scale]
    unfold inputRate
    ring
  let d (s : ℝ) (i : Fin k) := (M.muN n i - M.thetaN n i) * qq s i - M.muN n i * xx s i
  have hdint (t : ℝ) (ht : 0 ≤ t) (i : Fin k) : IntervalIntegrable (fun s => d s i) volume 0 t :=
    ((hint t ht i).2.2.const_mul _).sub ((hint t ht i).1.const_mul _)
  have hE (t : ℝ) (ht : 0 ≤ t) (i : Fin k) :
      xx t i = W ω t i + ∫ s in (0 : ℝ)..t, d s i := by
    rw [hbalance t ht i]
    dsimp only [d]
    rw [intervalIntegral.integral_sub ((hint t ht i).2.2.const_mul _) ((hint t ht i).1.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have he : (∫ s in (0 : ℝ)..t, pp s i) =
        (∫ s in (0 : ℝ)..t, xx s i) - ∫ s in (0 : ℝ)..t, qq s i := by
      simp_rw [hpp]
      exact intervalIntegral.integral_sub (hint t ht i).1 (hint t ht i).2.2
    rw [he]
    ring
  have hPhi (s : ℝ) (hs : 0 ≤ s) :
      qq s i = max (∑ j, xx s j) 0 * uProc n u0 X Ψ ω s i := by
    rw [← hq s hs]
    unfold uProc
    split_ifs with h
    · have hsum : ∑ j, qq s j = (∑ j, X ω s j - n) / r := by
        simp only [qq, Phihat, ← Finset.sum_div, ← hWork ω s hs, max_eq_left h.le, r]
      rw [hsum]
      dsimp [qq, Phihat, r]
      field_simp
    · have hsum : ∑ j, qq s j = 0 := by
        simp only [qq, Phihat, ← Finset.sum_div, ← hWork ω s hs, max_eq_right (le_of_not_gt h), zero_div]
      have hi : qq s i = 0 := by
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hqn s hs j)] at hsum
        exact hsum i (Finset.mem_univ i)
      rw [hi, hsum, zero_mul]
  have he : (∫ s in (0:ℝ)..t,
        drift M.diffData (M.Xhat n X ω s) (uProc n u0 X Ψ ω s) i +
        (inputRate M n i - M.ell i) +
          ((M.muN n i - M.thetaN n i) - (M.mu i - M.theta i)) * Phihat n X Ψ ω s i -
          (M.muN n i - M.mu i) * M.Xhat n X ω s i) =
      inputRate M n i * t + ∫ s in (0:ℝ)..t, d s i := by
    calc
      _ = ∫ s in (0:ℝ)..t, inputRate M n i + d s i := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht] at hs
        change M.ell i + (M.mu i - M.theta i) * max (∑ j, xx s j) 0 *
          uProc n u0 X Ψ ω s i - M.mu i * xx s i + (inputRate M n i - M.ell i) +
          ((M.muN n i - M.thetaN n i) - (M.mu i - M.theta i)) * qq s i -
          (M.muN n i - M.mu i) * xx s i = _
        rw [mul_assoc (M.mu i - M.theta i), ← hPhi s hs.1]
        dsimp [d]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hdint t ht i)]
        simp [intervalIntegral.integral_const, mul_comm t]
  rw [he]
  have h := hE t ht i
  dsimp only [W, xx] at h
  linarith

set_option maxHeartbeats 1500000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (u0 : Fin k → ℝ) :
    UocInProb M.P (fun n ω t i => M.Xhat n (X n) ω t i - M.Xhat0 n (X0 n) i -
        (M.Ahat n ω t i - M.Rhat n ω (queueTime (X n) (Ψ n) ω i t / (n:ℝ)) i -
        M.Shat n ω (busyTime (Ψ n) ω i t / (n:ℝ)) i) -
        ∫ s in (0:ℝ)..t, drift M.diffData (M.Xhat n (X n) ω s)
          (uProc n u0 (X n) (Ψ n) ω s) i) (fun _ => 0) := by
  let d (n : ℕ) (ω : Ω) (s : ℝ) (i : Fin k) :=
    drift M.diffData (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) i
  let E (n : ℕ) (ω : Ω) (s : ℝ) (i : Fin k) :=
    (inputRate M n i - M.ell i) +
      ((M.muN n i - M.thetaN n i) - (M.mu i - M.theta i)) * Phihat n (X n) (Ψ n) ω s i -
      (M.muN n i - M.mu i) * M.Xhat n (X n) ω s i
  let Z (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :=
    M.Xhat n (X n) ω t i - M.Xhat0 n (X0 n) i -
      (M.Ahat n ω t i - M.Rhat n ω (queueTime (X n) (Ψ n) ω i t / (n:ℝ)) i -
       M.Shat n ω (busyTime (Ψ n) ω i t / (n:ℝ)) i) - ∫ s in (0:ℝ)..t, d n ω s i
  have hqd (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (s : ℝ) (hs : 0 ≤ s) (i : Fin k) :
      Phihat n (X n) (Ψ n) ω s i = max (∑ j, M.Xhat n (X n) ω s j) 0 *
        uProc n u0 (X n) (Ψ n) ω s i := by
    have hR : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hX : (∑ j, M.Xhat n (X n) ω s j) = ((∑ j, X n ω s j)-n)/Real.sqrt n := by
      simp only [SystemSequence.Xhat, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul,
        show ∑ j, M.rho j = 1 from M.sum_rho, one_mul]
    rw [hX]
    unfold uProc
    split_ifs with h
    · rw [max_eq_left (div_nonneg h.le hR.le)]
      dsimp [Phihat]
      field_simp
    · have hzero : ∑ j, (X n ω s j - Ψ n ω s j) = 0 := by
        rw [← hWork n hn ω s hs, max_eq_right (le_of_not_gt h)]
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => (hC n hn).phi_nonneg ω s j hs)).1 hzero i (Finset.mem_univ i)
      rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hR.le), zero_mul]
      simp [Phihat, hi]
  have hZ (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (i : Fin k) :
      Z n ω t i = ∫ s in (0:ℝ)..t, E n ω s i := by
    have hI := (hC n hn).integrable ω i t ht
    have hΦ : IntervalIntegrable (fun s => Phihat n (X n) (Ψ n) ω s i) volume 0 t :=
      hI.2.div_const _
    have hX : IntervalIntegrable (fun s => M.Xhat n (X n) ω s i) volume 0 t := by
      have hx := ((hI.2.add hI.1).sub (intervalIntegrable_const (c := M.rho i*n))).div_const (Real.sqrt n)
      simpa [SystemSequence.Xhat] using hx
    have hEint : IntervalIntegrable (fun s => E n ω s i) volume 0 t :=
      (intervalIntegrable_const.add (hΦ.const_mul _)).sub (hX.const_mul _)
    have hd : IntervalIntegrable (fun s => d n ω s i) volume 0 t := by
      refine (intervalIntegrable_congr ?_).2
        (((intervalIntegrable_const (c := M.ell i)).add (hΦ.const_mul (M.mu i-M.theta i))).sub (hX.const_mul (M.mu i)))
      intro s hs
      rw [uIoc_of_le ht] at hs
      dsimp [d, drift, SystemSequence.diffData]
      rw [mul_assoc, ← hqd n hn ω s hs.1.le i]
    have heq := diffusion_drift_equation M n hn (X0 n) (X n) (Ψ n) (hC n hn)
      (hWork n hn) u0 ω t ht i
    have hiEq : (∫ s in (0:ℝ)..t,
        d n ω s i + (inputRate M n i - M.ell i) +
          ((M.muN n i - M.thetaN n i) - (M.mu i - M.theta i)) * Phihat n (X n) (Ψ n) ω s i -
          (M.muN n i - M.mu i) * M.Xhat n (X n) ω s i) =
        (∫ s in (0:ℝ)..t, d n ω s i) + ∫ s in (0:ℝ)..t, E n ω s i := by
      rw [← intervalIntegral.integral_add hd hEint]
      apply intervalIntegral.integral_congr
      intro s hs
      unfold E
      ring
    rw [hiEq] at heq
    unfold Z
    linarith
  change UocInProb M.P Z (fun _ => 0)
  intro T hT ε hε
  refine tendsto_order.2 ⟨fun _ hh => (not_lt_zero hh).elim, fun η hη => ?_⟩
  have hq (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (t : ℝ) (i : Fin k) (ht : 0 ≤ t) :
      X n ω t i - Ψ n ω t i ≤ max ((∑ j, X n ω t j) - n) 0 := by
    rw [hWork n hn ω t ht]
    exact Finset.single_le_sum (fun j _ => (hC n hn).phi_nonneg ω t j ht) (Finset.mem_univ i)
  obtain ⟨B, hB, hGood⟩ := controlled_compact_containment M X0 x hX0 X Ψ hC hq T hT η hη
  let D : ℝ := (k:ℝ)*T*(1 + (k:ℝ)*B+B) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let a := ε/(2*D)
  have ha : 0 < a := by dsimp [a]; positivity
  have hRate : ∀ᶠ n in atTop, ∀ i : Fin k,
      |inputRate M n i - M.ell i| < a ∧
      |(M.muN n i - M.thetaN n i) - (M.mu i - M.theta i)| < a ∧
      |M.muN n i - M.mu i| < a := by
    rw [Filter.eventually_all]
    intro i
    have h1 := (Metric.tendsto_nhds.mp (inputRate_tendsto M i)) a ha
    have h2 := (Metric.tendsto_nhds.mp ((M.mu_lim i).sub (M.theta_lim i))) a ha
    have h3 := (Metric.tendsto_nhds.mp (M.mu_lim i)) a ha
    filter_upwards [h1,h2,h3] with n h1 h2 h3
    simpa only [Real.dist_eq] using And.intro h1 (And.intro h2 h3)
  filter_upwards [hGood,hRate,eventually_ge_atTop (1:ℕ)] with n hGood hRate hn
  refine lt_of_le_of_lt (measure_mono ?_) hGood
  intro ω hω
  by_contra hb
  have hState (s : ℝ) (hs : s ∈ Icc 0 T) : ‖M.Xhat n (X n) ω s‖ ≤ B :=
    le_of_not_gt fun hgt => hb ⟨s,hs,hgt⟩
  have hXb (s : ℝ) (hs : s ∈ Icc 0 T) (i : Fin k) : |M.Xhat n (X n) ω s i| ≤ B :=
    (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (M.Xhat n (X n) ω s) i :
      |M.Xhat n (X n) ω s i| ≤ ‖M.Xhat n (X n) ω s‖).trans (hState s hs)
  have hPb (s : ℝ) (hs : s ∈ Icc 0 T) (i : Fin k) : |Phihat n (X n) (Ψ n) ω s i| ≤ (k:ℝ)*B := by
    have hR : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hx : (∑ j, M.Xhat n (X n) ω s j) = ((∑ j, X n ω s j)-n)/Real.sqrt n := by
      simp only [SystemSequence.Xhat, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul,
        show ∑ j, M.rho j = 1 from M.sum_rho, one_mul]
    unfold Phihat
    rw [abs_of_nonneg (div_nonneg ((hC n hn).phi_nonneg ω s i hs.1) hR.le)]
    refine (div_le_div_of_nonneg_right (hq n hn ω s i hs.1) hR.le).trans ?_
    rw [← max_div_div_right hR.le, zero_div, ← hx]
    apply max_le _ (by positivity)
    calc
      _ ≤ ∑ _ : Fin k, B := Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hXb s hs i)
      _ = _ := by simp
  let L := a*(1+(k:ℝ)*B+B)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hEb (s : ℝ) (hs : s ∈ Icc 0 T) (i : Fin k) : |E n ω s i| ≤ L := by
    have hh1 := (hRate i).1.le
    have hh2 := (hRate i).2.1.le
    have hh3 := (hRate i).2.2.le
    have hh4 := mul_le_mul hh2 (hPb s hs i) (abs_nonneg _) ha.le
    have hh5 := mul_le_mul hh3 (hXb s hs i) (abs_nonneg _) ha.le
    calc
      _ ≤ |inputRate M n i - M.ell i| +
        |(M.muN n i - M.thetaN n i) - (M.mu i - M.theta i)| * |Phihat n (X n) (Ψ n) ω s i| +
        |M.muN n i - M.mu i| * |M.Xhat n (X n) ω s i| := by
        unfold E
        refine (abs_sub _ _).trans ?_
        refine (add_le_add_left (abs_add_le _ _) _).trans_eq ?_
        rw [abs_mul, abs_mul]
      _ ≤ L := by dsimp [L]; linarith
  have hsup : supDist (Z n ω) (fun _ => 0) T ≤ ENNReal.ofReal (ε/2) := by
    apply iSup₂_le
    intro t ht
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ∑ _ : Fin k, T*L := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [Pi.zero_apply, sub_zero, hZ n hn ω t ht.1 i]
        have hI := (hC n hn).integrable ω i t ht.1
        have hΦ : IntervalIntegrable (fun s => Phihat n (X n) (Ψ n) ω s i) volume 0 t := hI.2.div_const _
        have hX : IntervalIntegrable (fun s => M.Xhat n (X n) ω s i) volume 0 t := by
          simpa [SystemSequence.Xhat] using
            (((hI.2.add hI.1).sub (intervalIntegrable_const (c := M.rho i*n))).div_const (Real.sqrt n))
        have hEint : IntervalIntegrable (fun s => E n ω s i) volume 0 t :=
          (intervalIntegrable_const.add (hΦ.const_mul _)).sub (hX.const_mul _)
        have hInt := intervalIntegral.integral_mono_on ht.1 hEint.abs
          (intervalIntegrable_const (c := L)) (fun s hs => hEb s ⟨hs.1, hs.2.trans ht.2⟩ i)
        refine (intervalIntegral.abs_integral_le_integral_abs ht.1).trans (hInt.trans ?_)
        simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using
          mul_le_mul_of_nonneg_right ht.2 hL
      _ = (k:ℝ)*T*L := by simp [mul_assoc]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (show (k:ℝ)*T*(1+(k:ℝ)*B+B) ≤ D by dsimp [D]; linarith) ha.le
        have he : D*a = ε/2 := by dsimp [a]; field_simp
        rw [he] at h
        dsimp [L]
        nlinarith
  exact (not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith))) (hω.trans hsup)
