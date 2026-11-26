-- Prove2me | solution 1 for ManyServerQED.Scheduling.centered_queue_arrival_noise_restarted_clock_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:10:14.259797+00:00
-- url     : https://prove2.me/submissions/7e9f4e91-bef2-4706-8703-887afd283705

import Theorems.Thm_ManyServerQED_Scheduling_next_arrival_residual_vanishes
import Theorems.Thm_ManyServerQED_Scheduling_queue_arrival_norm_and_modulus_bounds
import Theorems.Thm_ManyServerQED_Scheduling_finite_family_independent_continuous_brownian
import Theorems.Thm_ManyServerQED_Scheduling_asymptotic_modulus_transfers_uniform_random_clock_evaluations
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 1500000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k)
    (mL mU : ℝ) (hA3 : M.Assumption3 mL mU)
    (i : Fin k) (b : ℝ) (hb : 0 ≤ b) (T : ℝ) (hT : b ≤ T) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => M.P {ω | ∃ t ∈ Icc b T,
      ε ≤ |M.Ahat n ω (M.nextArrival n i ω b+(t-b)) i-M.Ahat n ω t i|}) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure M.P := M.isProb
  have hP : 0 ≤ T := hb.trans hT
  have hge (n : ℕ) (ω : Ω) : b ≤ M.nextArrival n i ω b := by
    have ht : Tendsto (M.arrivalEpoch n i ω) atTop atTop := by
      have he (m : ℕ) : M.arrivalEpoch n i ω m =
          partialSum (fun j => M.U i j ω) m / M.lamN n i := by
        simp only [SystemSequence.arrivalEpoch,partialSum,← Finset.sum_div]
      rw [show M.arrivalEpoch n i ω = fun m => partialSum (fun j => M.U i j ω) m / M.lamN n i from funext he]
      exact Filter.Tendsto.atTop_div_const (M.lamN_pos n i) (M.U_finite i ω)
    obtain ⟨N,hN⟩ := eventually_atTop.1 (ht (eventually_ge_atTop b))
    have hN' := hN (max N 1) (le_max_left _ _)
    apply le_csInf
    · exact ⟨M.arrivalEpoch n i ω (max N 1),hN',max N 1,le_max_right _ _,rfl⟩
    · intro t ht
      exact ht.1
  let A (n : ℕ) (ω : Ω) (t : ℝ) := M.Ahat n ω t i
  let v (_ : ℕ) (_ : Ω) (t : ℝ) := t
  let u (n : ℕ) (ω : Ω) (t : ℝ) := t+ (M.nextArrival n i ω b-b)
  have hu : ∀ᶠ n in atTop, ∀ ω t, t ∈ Icc (0:ℝ) T → 0 ≤ u n ω t :=
    Eventually.of_forall (fun n ω t ht => add_nonneg ht.1 (sub_nonneg.2 (hge n ω)))
  have hv : ∀ᶠ n in atTop, ∀ ω t, t ∈ Icc (0:ℝ) T → v n ω t ∈ Icc (0:ℝ) T :=
    Eventually.of_forall (fun _ _ _ h => h)
  have hU (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => M.P {ω | ∃ t ∈ Icc (0:ℝ) T, δ ≤ |u n ω t-v n ω t|}) atTop (𝓝 0) := by
    have h := next_arrival_residual_vanishes M mL mU hA3 i b hb δ hδ
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    intro n
    apply measure_mono
    rintro ω ⟨t,ht,he⟩
    dsimp [u,v] at he
    rwa [add_sub_cancel_left,abs_of_nonneg (sub_nonneg.2 (hge n ω))] at he
  obtain ⟨Λ,mΛ,P,B,hP,hB,hBc,_,_⟩ := finite_family_independent_continuous_brownian 1
  letI := mΛ
  letI : IsProbabilityMeasure P := hP
  have hMod (K : ℕ) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
      ∃ δ > 0, ∀ᶠ n in atTop,
        M.P {ω | ∃ s ∈ Icc (0:ℝ) (K:ℝ), ∃ t ∈ Icc (0:ℝ) (K:ℝ), |s-t| ≤ δ ∧
          ε ≤ dist (A n ω s) (A n ω t)} ≤ ENNReal.ofReal η := by
    obtain ⟨C,hC,δ,hδ,h⟩ := queue_arrival_norm_and_modulus_bounds M i
      (hB 0) (hBc 0) K (Nat.cast_nonneg _) ε η hε hη
    refine ⟨δ,hδ,?_⟩
    filter_upwards [h] with n hn
    refine (measure_mono ?_).trans hn
    intro ω hw
    exact Or.inr (by simpa only [mem_setOf_eq,A,Real.dist_eq] using hw)
  intro ε hε
  have h := asymptotic_modulus_transfers_uniform_random_clock_evaluations M.P A hMod u v T hu hv hU ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le) fun n => ?_
  refine measure_mono ?_
  rintro ω ⟨t,ht,he⟩
  refine ⟨t,⟨hb.trans ht.1,ht.2⟩,?_⟩
  simpa only [u,v,A,Real.dist_eq,
    show t+(M.nextArrival n i ω b-b) = M.nextArrival n i ω b+(t-b) by ring] using he
