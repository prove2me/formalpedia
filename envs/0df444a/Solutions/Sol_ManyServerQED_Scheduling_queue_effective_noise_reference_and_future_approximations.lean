-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_effective_noise_reference_and_future_approximations
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:27:37.67805+00:00
-- url     : https://prove2.me/submissions/5f1253b5-dd1c-403d-ba1a-5f1225c6e204

import Theorems.Thm_ManyServerQED_Scheduling_centered_queue_service_noise_clock_approximations
import Theorems.Thm_ManyServerQED_Scheduling_centered_queue_arrival_noise_restarted_clock_approximation
import Theorems.Thm_ManyServerQED_Scheduling_abandonment_noise_vanishes_uoc
import Mathlib
open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal
open Finset

set_option maxHeartbeats 1250000 in
private theorem finite_sum_uniform_errors {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {I : Type*} [Fintype I]
    (D : I → ℕ → Ω → ℝ → ℝ) (S : Set ℝ)
    (h : ∀ i ε, 0 < ε → Tendsto
      (fun n => P {ω | ∃ t ∈ S, ε ≤ |D i n ω t|}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => P {ω | ∃ t ∈ S, ε ≤ |∑ i, D i n ω t|}) atTop (𝓝 0) := by
  classical
  intro ε hε
  let a : ℝ := ε/((Fintype.card I:ℝ)+1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hFac : (Fintype.card I:ℝ)*a < ε := by
    have h := div_mul_cancel₀ ε (by positivity : (Fintype.card I:ℝ)+1 ≠ 0)
    change a*((Fintype.card I:ℝ)+1) = ε at h
    rw [mul_add,mul_one] at h
    nlinarith
  let H (i : I) (n : ℕ) := P {ω | ∃ t ∈ S, a ≤ |D i n ω t|}
  have hSum : Tendsto (fun n => ∑ i, H i n) atTop (𝓝 0) := by
    simpa using (tendsto_finsetSum Finset.univ (fun i _ => h i a ha))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSum
    (fun _ => bot_le) fun n => ?_
  let B (i : I) : Set Ω := {ω | ∃ t ∈ S, a ≤ |D i n ω t|}
  have hU : P (⋃ i, B i) ≤ ∑ i, H i n := by
    simpa only [tsum_fintype,H,B] using (measure_iUnion_le (μ := P) B)
  refine (measure_mono ?_).trans hU
  rintro ω ⟨t,ht,hεt⟩
  apply mem_iUnion.2
  by_contra! hnone
  have hB (i : I) : |D i n ω t| ≤ a :=
    (lt_of_not_ge (fun h' => hnone i ⟨t,ht,h'⟩)).le
  have hSum : |∑ i, D i n ω t| ≤ (Fintype.card I:ℝ)*a := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simpa only [sum_const,card_univ,nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hB i))
  exact (not_lt_of_ge hεt) (hSum.trans_lt hFac)

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 1750000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (mL mU : ℝ) (hA3 : M.Assumption3 mL mU)
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (i : Fin k) (b : ℝ) (hb : 0 ≤ b) (T : ℝ) (hT : b ≤ T) :
    let A (n : ℕ) (ω : Ω) (t : ℝ) := M.Ahat n ω t i
    let S (n : ℕ) (ω : Ω) (t : ℝ) := M.Shat n ω t i
    let R (n : ℕ) (ω : Ω) (t : ℝ) :=
      M.Rhat n ω (queueTime (X n) (Ψ n) ω i t/(n:ℝ)) i
    let c (n : ℕ) (ω : Ω) (t : ℝ) := busyTime (Ψ n) ω i t/(n:ℝ)
    let w (n : ℕ) (ω : Ω) (t : ℝ) := (A n ω t-S n ω (c n ω t)-R n ω t)/M.diffData.r i
    let z (n : ℕ) (ω : Ω) (t : ℝ) := (A n ω t-S n ω (M.rho i*t))/M.diffData.r i
    let a (n : ℕ) (ω : Ω) := M.nextArrival n i ω b
    let V (n : ℕ) (ω : Ω) (t : ℝ) :=
      (A n ω (a n ω+(t-b))-A n ω (a n ω) -
        (S n ω (c n ω b+M.rho i*(t-b))-S n ω (c n ω b)))/M.diffData.r i
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, ε ≤ |w n ω t-z n ω t|}) atTop (𝓝 0) ∧
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, ε ≤ |V n ω t-(w n ω t-w n ω b)|})
        atTop (𝓝 0) := by
  intro A S R c w z a V
  let r := M.diffData.r i
  have hr : 0 < r := M.diffData.r_pos i
  have hR (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, δ ≤ |R n ω t|}) atTop (𝓝 0) := by
    have h := abandonment_noise_vanishes_uoc M X0 x hX0 X Ψ hC hWork T (hb.trans hT) δ hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
      fun n => measure_mono ?_
    rintro ω ⟨t,ht,he⟩
    refine (ENNReal.ofReal_le_ofReal (he.trans ?_)).trans
      (le_iSup_of_le t (le_iSup_of_le (show t ∈ Icc (0:ℝ) T from ⟨hb.trans ht.1,ht.2⟩) le_rfl))
    change |R n ω t| ≤ ∑ j, |M.Rhat n ω (queueTime (X n) (Ψ n) ω j t/(n:ℝ)) j-0|
    simpa only [R,sub_zero] using
      (Finset.single_le_sum
        (f := fun j => |M.Rhat n ω (queueTime (X n) (Ψ n) ω j t/(n:ℝ)) j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hS := centered_queue_service_noise_clock_approximations M X0 x hX0 X Ψ hC hWork i b hb T hT
  have hA := centered_queue_arrival_noise_restarted_clock_approximation M mL mU hA3 i b hb T hT
  have hNeg {E : ℕ → Ω → ℝ → ℝ}
      (h : ∀ δ > (0:ℝ), Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, δ ≤ |E n ω t|}) atTop (𝓝 0)) :
      ∀ δ > (0:ℝ), Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, δ ≤ |-E n ω t|}) atTop (𝓝 0) := by
    simpa only [abs_neg] using h
  have hBase {E : ℕ → Ω → ℝ → ℝ}
      (h : ∀ δ > (0:ℝ), Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, δ ≤ |E n ω t|}) atTop (𝓝 0)) :
      ∀ δ > (0:ℝ), Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T, δ ≤ |E n ω b|}) atTop (𝓝 0) := by
    intro δ hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h δ hδ)
      (fun _ => bot_le) fun n => measure_mono ?_
    rintro ω ⟨t,ht,he⟩
    exact ⟨b,⟨le_rfl,hT⟩,he⟩
  let E (j : Fin 2) (n : ℕ) (ω : Ω) (t : ℝ) :=
    ![-(S n ω (c n ω t)-S n ω (M.rho i*t)),-R n ω t] j
  have hE (j : Fin 2) : ∀ δ > (0:ℝ), Tendsto
      (fun n => M.P {ω | ∃ t ∈ Icc b T, δ ≤ |E j n ω t|}) atTop (𝓝 0) := by
    fin_cases j
    · simpa only [E,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using hNeg (fun δ hδ => (hS δ hδ).1)
    · simpa only [E,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using hNeg hR
  let F (j : Fin 5) (n : ℕ) (ω : Ω) (t : ℝ) :=
    ![A n ω (a n ω+(t-b))-A n ω t,
      -(A n ω (a n ω+(b-b))-A n ω b),
      S n ω (c n ω t)-S n ω (c n ω b+M.rho i*(t-b)),
      R n ω t,-R n ω b] j
  have hF (j : Fin 5) : ∀ δ > (0:ℝ), Tendsto
      (fun n => M.P {ω | ∃ t ∈ Icc b T, δ ≤ |F j n ω t|}) atTop (𝓝 0) := by
    fin_cases j
    · simpa only [F,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using hA
    · simpa only [F,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using hNeg (hBase hA)
    · simpa only [F,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using (fun δ hδ => (hS δ hδ).2)
    · simpa only [F,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using hR
    · simpa only [F,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using hNeg (hBase hR)
  have hE' (n : ℕ) (ω : Ω) (t : ℝ) :
      w n ω t-z n ω t = (∑ j, E j n ω t)/r := by
    simp only [Fin.sum_univ_two,E,Matrix.cons_val_zero,Matrix.cons_val_succ,w,z]
    dsimp [r]
    ring
  have hF' (n : ℕ) (ω : Ω) (t : ℝ) :
      V n ω t-(w n ω t-w n ω b) = (∑ j, F j n ω t)/r := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,F,Matrix.cons_val_zero,
      Matrix.cons_val_succ,sub_self,add_zero,V,w]
    dsimp [r]
    ring
  intro ε hε
  constructor
  · simp_rw [hE',abs_div,abs_of_nonneg hr.le,le_div_iff₀ hr]
    exact finite_sum_uniform_errors M.P E (Icc b T) hE (ε*r) (mul_pos hε hr)
  · simp_rw [hF',abs_div,abs_of_nonneg hr.le,le_div_iff₀ hr]
    exact finite_sum_uniform_errors M.P F (Icc b T) hF (ε*r) (mul_pos hε hr)
