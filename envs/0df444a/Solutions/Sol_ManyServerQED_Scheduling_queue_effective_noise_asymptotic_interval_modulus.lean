-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_effective_noise_asymptotic_interval_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:40:58.597181+00:00
-- url     : https://prove2.me/submissions/4782553a-50e3-4e36-bdbe-b1080d52260e

import Theorems.Thm_ManyServerQED_Scheduling_queue_effective_noise_reference_and_future_approximations
import Theorems.Thm_ManyServerQED_Scheduling_queue_arrival_norm_and_modulus_bounds
import Theorems.Thm_ManyServerQED_Scheduling_poisson_rows_centered_interval_modulus_bound
import Theorems.Thm_ManyServerQED_Scheduling_poisson_primitive_deterministic_clock_change
import Theorems.Thm_ManyServerQED_Scheduling_finite_family_independent_continuous_brownian
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 1800000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (mL mU : ℝ) (hA3 : M.Assumption3 mL mU)
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (i : Fin k) (T : ℕ) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    let w (n : ℕ) (ω : Ω) (t : ℝ) :=
      (M.Ahat n ω t i-M.Shat n ω (busyTime (Ψ n) ω i t/(n:ℝ)) i-
        M.Rhat n ω (queueTime (X n) (Ψ n) ω i t/(n:ℝ)) i)/M.diffData.r i
    ∃ δ > 0, ∀ᶠ n in atTop,
      M.P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ |w n ω s-w n ω t|} ≤ ENNReal.ofReal η := by
  intro w
  letI : IsProbabilityMeasure M.P := M.isProb
  let r := M.diffData.r i
  have hr : 0 < r := M.diffData.r_pos i
  have hρ : 0 ≤ M.rho i := (div_pos (M.lam_pos i) (M.mu_pos i)).le
  have hρ1 : M.rho i ≤ 1 := by
    rw [← M.sum_rho]
    change M.lam i/M.mu i ≤ _
    exact Finset.single_le_sum (fun j _ => (div_pos (M.lam_pos j) (M.mu_pos j)).le)
      (Finset.mem_univ i)
  let A (n : ℕ) (ω : Ω) (t : ℝ) := M.Ahat n ω t i
  let S (n : ℕ) (ω : Ω) (t : ℝ) := M.Shat n ω t i
  let v (n : ℕ) (ω : Ω) (t : ℝ) := (A n ω t-S n ω (M.rho i*t))/r
  let a := (r*ε)/4
  let b := η/3
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨Λ,mΛ,P,B,hP,hB,hBc,_,_⟩ := finite_family_independent_continuous_brownian 1
  letI := mΛ
  letI : IsProbabilityMeasure P := hP
  obtain ⟨_,_,δ,hδ,hA⟩ := queue_arrival_norm_and_modulus_bounds M i
    (hB 0) (hBc 0) T (Nat.cast_nonneg _) a b ha hb
  let N (ω : Ω) (t : ℝ) := M.S 1 i ω ((M.muN 1 i)⁻¹*t)
  have hN : IsPoissonProcess M.P N 1 := by
    have h := poisson_primitive_deterministic_clock_change (M.S_poisson 1 i)
      (M.muN 1 i)⁻¹ (inv_pos.2 (M.muN_pos 1 i))
    simpa only [mul_inv_cancel₀ (M.muN_pos 1 i).ne'] using h
  obtain ⟨δ',hδ',hS⟩ := poisson_rows_centered_interval_modulus_bound
    (fun n => M.S n i) (fun n => M.muN n i) (fun n => M.S_poisson n i)
    (M.mu i) (M.mu_pos i).le (M.mu_lim i) N hN (hB 0) (hBc 0) T a b ha hb
  have hE := (queue_effective_noise_reference_and_future_approximations M mL mU hA3
    X0 x hX0 X Ψ hC hWork i 0 le_rfl T (Nat.cast_nonneg _) (ε/4) (by positivity)).1
  have hE' : ∀ᶠ n in atTop,
      M.P {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), ε/4 ≤ |w n ω t-v n ω t|} ≤ ENNReal.ofReal b :=
    ((tendsto_order.1 hE).2 (ENNReal.ofReal b) (ENNReal.ofReal_pos.2 hb)).mono (fun n hn => hn.le)
  refine ⟨min δ δ',lt_min hδ hδ',?_⟩
  filter_upwards [hA,hS,hE'] with n hnA hnS hnE
  let BA : Set Ω := {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
    |s-t| ≤ δ ∧ a ≤ |A n ω s-A n ω t|}
  let BS : Set Ω := {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
    |s-t| ≤ δ' ∧ a ≤ |S n ω s-S n ω t|}
  let BE : Set Ω := {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), ε/4 ≤ |w n ω t-v n ω t|}
  have bA : M.P BA ≤ ENNReal.ofReal b := (measure_mono (fun ω h => Or.inr h)).trans hnA
  have bS : M.P BS ≤ ENNReal.ofReal b := hnS
  have bE : M.P BE ≤ ENNReal.ofReal b := hnE
  have hSum : M.P ((BA ∪ BS) ∪ BE) ≤ ENNReal.ofReal η := by
    refine (measure_union_le _ _).trans ((add_le_add (measure_union_le _ _) le_rfl).trans ?_)
    refine (add_le_add (add_le_add bA bS) bE).trans_eq ?_
    rw [← ENNReal.ofReal_add hb.le hb.le,← ENNReal.ofReal_add (add_nonneg hb.le hb.le) hb.le]
    congr 1
    dsimp [b]
    ring
  refine (measure_mono ?_).trans hSum
  rintro ω ⟨s,hs,t,ht,hst,hεw⟩
  by_contra hh
  have ha0 : |A n ω s-A n ω t| < a :=
    lt_of_not_ge fun bad => hh (Or.inl (Or.inl ⟨s,hs,t,ht,hst.trans (min_le_left _ _),bad⟩))
  have htime (u : ℝ) (hu : u ∈ Icc (0:ℝ) (T:ℝ)) : M.rho i*u ∈ Icc (0:ℝ) (T:ℝ) :=
    ⟨mul_nonneg hρ hu.1,(mul_le_of_le_one_left hu.1 hρ1).trans hu.2⟩
  have hΔ : |M.rho i*s-M.rho i*t| ≤ δ' := by
    rw [← mul_sub,abs_mul,abs_of_nonneg hρ]
    exact (mul_le_of_le_one_left (abs_nonneg _) hρ1).trans (hst.trans (min_le_right _ _))
  have hs0 : |S n ω (M.rho i*s)-S n ω (M.rho i*t)| < a :=
    lt_of_not_ge fun bad => hh (Or.inl (Or.inr ⟨_,htime s hs,_,htime t ht,hΔ,bad⟩))
  have hv0 : |v n ω s-v n ω t| < ε/2 := by
    have he : v n ω s-v n ω t =
        ((A n ω s-A n ω t)-(S n ω (M.rho i*s)-S n ω (M.rho i*t)))/r := by dsimp [v]; ring
    rw [he,abs_div,abs_of_nonneg hr.le,div_lt_iff₀ hr]
    have h := abs_sub (A n ω s-A n ω t) (S n ω (M.rho i*s)-S n ω (M.rho i*t))
    dsimp [a] at ha0 hs0
    linarith
  have heS : |w n ω s-v n ω s| < ε/4 := lt_of_not_ge fun bad => hh (Or.inr ⟨s,hs,bad⟩)
  have heT : |w n ω t-v n ω t| < ε/4 := lt_of_not_ge fun bad => hh (Or.inr ⟨t,ht,bad⟩)
  have he : w n ω s-w n ω t = (w n ω s-v n ω s)+
      (v n ω s-v n ω t)-(w n ω t-v n ω t) := by ring
  rw [he] at hεw
  have h1 := abs_sub ((w n ω s-v n ω s)+(v n ω s-v n ω t)) (w n ω t-v n ω t)
  have h2 := abs_add_le (w n ω s-v n ω s) (v n ω s-v n ω t)
  linarith
