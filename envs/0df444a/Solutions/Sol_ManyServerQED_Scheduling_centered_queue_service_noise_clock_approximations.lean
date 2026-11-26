-- Prove2me | solution 1 for ManyServerQED.Scheduling.centered_queue_service_noise_clock_approximations
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:51:39.924377+00:00
-- url     : https://prove2.me/submissions/889463fa-9c09-46f8-ac94-21983abb274e

import Theorems.Thm_ManyServerQED_Scheduling_queue_time_changes_uoc
import Theorems.Thm_ManyServerQED_Scheduling_poisson_rows_centered_interval_modulus_bound
import Theorems.Thm_ManyServerQED_Scheduling_poisson_primitive_deterministic_clock_change
import Theorems.Thm_ManyServerQED_Scheduling_finite_family_independent_continuous_brownian
import Theorems.Thm_ManyServerQED_Scheduling_asymptotic_modulus_transfers_uniform_random_clock_evaluations

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem clock_probability_of_pointwise_comparison {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {F G : ℕ → Ω → ℝ → ℝ} {b T : ℝ}
    (h : ∀ ε > (0:ℝ),
      Tendsto (fun n => P {ω | ∃ t ∈ Icc b T, ε ≤ |F n ω t|}) atTop (𝓝 0))
    (h' : ∀ ε > (0:ℝ),
      Tendsto (fun n => P {ω | ∃ t ∈ Icc b T, ε ≤ |G n ω t|}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ∃ t ∈ Icc b T, ε ≤ |F n ω t-G n ω t|}) atTop (𝓝 0) := by
  have hb := (h (ε/2) (half_pos hε)).add (h' (ε/2) (half_pos hε))
  rw [add_zero] at hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => bot_le) fun n => ?_
  refine (measure_mono ?_).trans (measure_union_le _ _)
  rintro ω ⟨t,ht,hp⟩
  by_cases hf : ε/2 ≤ |F n ω t|
  · exact Or.inl ⟨t,ht,hf⟩
  · have hh := abs_sub (F n ω t) (G n ω t)
    exact Or.inr ⟨t,ht,by linarith [lt_of_not_ge hf]⟩

set_option maxHeartbeats 2000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (i : Fin k) (b : ℝ) (hb : 0 ≤ b) (T : ℝ) (hT : b ≤ T) :
    let a (n : ℕ) (ω : Ω) (t : ℝ) := busyTime (Ψ n) ω i t / (n:ℝ)
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, ε ≤
        |M.Shat n ω (a n ω t) i - M.Shat n ω (M.rho i*t) i|}) atTop (𝓝 0) ∧
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, ε ≤
        |M.Shat n ω (a n ω t) i -
          M.Shat n ω (a n ω b+M.rho i*(t-b)) i|}) atTop (𝓝 0) := by
  intro a
  letI : IsProbabilityMeasure M.P := M.isProb
  have hTime := (queue_time_changes_uoc M X0 x hX0 X Ψ hC hWork).1
  have hTP : 0 ≤ T := hb.trans hT
  have hρ : 0 ≤ M.rho i := (div_pos (M.lam_pos i) (M.mu_pos i)).le
  have hρ1 : M.rho i ≤ 1 := by
    rw [← M.sum_rho]
    change M.lam i/M.mu i ≤ _
    exact Finset.single_le_sum (fun j _ => (div_pos (M.lam_pos j) (M.mu_pos j)).le)
      (Finset.mem_univ i)
  have htau (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
      0 ≤ a n ω t := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    unfold busyTime
    apply intervalIntegral.integral_nonneg ht
    exact fun s hs => (hC n hn).psi_nonneg ω s i hs.1
  have hE (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc (0:ℝ) T,
        δ ≤ |a n ω t-M.rho i*t|}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hTime T hTP δ hδ)
      (fun _ => bot_le) fun n => measure_mono ?_
    rintro ω ⟨t,ht,he⟩
    refine (ENNReal.ofReal_le_ofReal (he.trans ?_)).trans
      (le_iSup_of_le t (le_iSup_of_le ht le_rfl))
    change |a n ω t-M.rho i*t| ≤ ∑ j, |busyTime (Ψ n) ω j t/(n:ℝ)-M.rho j*t|
    exact Finset.single_le_sum (f := fun j => |busyTime (Ψ n) ω j t/(n:ℝ)-M.rho j*t|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hu : ∀ᶠ n in atTop, ∀ ω t, t ∈ Icc (0:ℝ) T → 0 ≤ a n ω t :=
    (eventually_ge_atTop 1).mono (fun n hn ω t ht => htau n hn ω t ht.1)
  let c (n : ℕ) (ω : Ω) (t : ℝ) := a n ω b+M.rho i*max (t-b) 0
  let v (_ : ℕ) (_ : Ω) (t : ℝ) := M.rho i*t
  let v' (_ : ℕ) (_ : Ω) (t : ℝ) := M.rho i*b+M.rho i*max (t-b) 0
  have hcu : ∀ᶠ n in atTop, ∀ ω t, t ∈ Icc (0:ℝ) T → 0 ≤ c n ω t :=
    (eventually_ge_atTop 1).mono (fun n hn ω t _ =>
      add_nonneg (htau n hn ω b hb) (mul_nonneg hρ (le_max_right _ _)))
  have hv : ∀ᶠ n in atTop, ∀ ω t, t ∈ Icc (0:ℝ) T → v n ω t ∈ Icc (0:ℝ) T := by
    exact Eventually.of_forall (fun n ω t ht =>
      ⟨mul_nonneg hρ ht.1,(mul_le_of_le_one_left ht.1 hρ1).trans ht.2⟩)
  have hv' : ∀ᶠ n in atTop, ∀ ω t, t ∈ Icc (0:ℝ) T → v' n ω t ∈ Icc (0:ℝ) T := by
    refine Eventually.of_forall (fun n ω t ht => ?_)
    have he : v' n ω t = M.rho i*max t b := by
      dsimp [v']
      rcases le_total t b with h | h
      · rw [max_eq_right h, max_eq_right (sub_nonpos.2 h),mul_zero,add_zero]
      · rw [max_eq_left h,max_eq_left (sub_nonneg.2 h)]
        ring
    rw [he]
    exact ⟨mul_nonneg hρ (ht.1.trans (le_max_left _ _)),
      (mul_le_of_le_one_left (ht.1.trans (le_max_left _ _)) hρ1).trans (max_le ht.2 hT)⟩
  have hE' (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc (0:ℝ) T,
        δ ≤ |c n ω t-v' n ω t|}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hE δ hδ)
      (fun _ => bot_le) fun n => measure_mono ?_
    rintro ω ⟨t,ht,he⟩
    refine ⟨b,⟨hb,hT⟩,?_⟩
    simpa only [c,v',add_sub_add_right_eq_sub] using he
  obtain ⟨Λ,mΛ,P,B,hP,hB,hBc,_,_⟩ := finite_family_independent_continuous_brownian 1
  letI := mΛ
  letI : IsProbabilityMeasure P := hP
  let N (ω : Ω) (t : ℝ) := M.S 1 i ω ((M.muN 1 i)⁻¹*t)
  have hN : IsPoissonProcess M.P N 1 := by
    have h := poisson_primitive_deterministic_clock_change (M.S_poisson 1 i)
      (M.muN 1 i)⁻¹ (inv_pos.2 (M.muN_pos 1 i))
    simpa only [mul_inv_cancel₀ (M.muN_pos 1 i).ne'] using h
  let S (n : ℕ) (ω : Ω) (t : ℝ) := M.Shat n ω t i
  have hMod (K : ℕ) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
      ∃ δ > 0, ∀ᶠ n in atTop,
        M.P {ω | ∃ s ∈ Icc (0:ℝ) (K:ℝ), ∃ t ∈ Icc (0:ℝ) (K:ℝ), |s-t| ≤ δ ∧
          ε ≤ dist (S n ω s) (S n ω t)} ≤ ENNReal.ofReal η := by
    simpa only [S,Real.dist_eq,SystemSequence.Shat] using
      poisson_rows_centered_interval_modulus_bound (fun n => M.S n i) (fun n => M.muN n i)
        (fun n => M.S_poisson n i) (M.mu i) (M.mu_pos i).le (M.mu_lim i) N hN
        (hB 0) (hBc 0) K ε η hε hη
  have h₁ := asymptotic_modulus_transfers_uniform_random_clock_evaluations M.P S hMod a v T hu hv hE
  have h₂ := asymptotic_modulus_transfers_uniform_random_clock_evaluations M.P S hMod c v' T hcu hv' hE'
  have hV (n : ℕ) (ω : Ω) (t : ℝ) (ht : b ≤ t) : v' n ω t = v n ω t := by
    dsimp [v',v]
    rw [max_eq_left (sub_nonneg.2 ht)]
    ring
  have h₃ (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, δ ≤ |S n ω (c n ω t)-S n ω (v n ω t)|})
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h₂ δ hδ)
      (fun _ => bot_le) fun n => measure_mono ?_
    rintro ω ⟨t,ht,he⟩
    exact ⟨t,⟨hb.trans ht.1,ht.2⟩,by simpa only [Real.dist_eq,hV n ω t ht.1] using he⟩
  have h₄ (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, δ ≤ |S n ω (a n ω t)-S n ω (v n ω t)|})
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h₁ δ hδ)
      (fun _ => bot_le) fun n => measure_mono ?_
    rintro ω ⟨t,ht,he⟩
    exact ⟨t,⟨hb.trans ht.1,ht.2⟩,by simpa only [Real.dist_eq] using he⟩
  intro ε hε
  refine ⟨h₄ ε hε,?_⟩
  have hh := clock_probability_of_pointwise_comparison M.P h₄ h₃ ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
    (fun _ => bot_le) fun n => measure_mono ?_
  rintro ω ⟨t,ht,he⟩
  refine ⟨t,ht,?_⟩
  have hc : c n ω t = a n ω b+M.rho i*(t-b) := by
    dsimp [c]
    rw [max_eq_left (sub_nonneg.2 ht.1)]
  rw [hc]
  convert he using 2
  ring
