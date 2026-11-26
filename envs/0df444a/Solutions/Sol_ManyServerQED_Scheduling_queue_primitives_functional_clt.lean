-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_primitives_functional_clt
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:12:26.33339+00:00
-- url     : https://prove2.me/submissions/c8237811-4738-4c2d-8db5-315398ff5adc

import Definitions.Def_ManyServerQED_Scheduling_Model
import Theorems.Thm_ManyServerQED_Scheduling_finite_family_independent_continuous_brownian
import Theorems.Thm_ManyServerQED_Scheduling_queue_primitives_joint_finite_observation_limit
import Theorems.Thm_ManyServerQED_Scheduling_queue_centered_primitives_are_cadlag
import Theorems.Thm_ManyServerQED_Scheduling_finite_coordinate_modulus_controls_vector_modulus
import Theorems.Thm_ManyServerQED_Scheduling_queue_arrival_norm_and_modulus_bounds
import Theorems.Thm_ManyServerQED_Scheduling_poisson_rows_centered_interval_modulus_bound
import Theorems.Thm_ManyServerQED_Scheduling_poisson_primitive_deterministic_clock_change
import Theorems.Thm_ManyServerQED_Scheduling_functional_coupling_from_fdd_and_interval_modulus

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 1500000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (B : Fin (k + k + k) → ℝ≥0 → Ω' → ℝ),
      IsProbabilityMeasure P' ∧ (∀ j, IsBrownianReal (B j) P') ∧
      iIndepFun (fun j ω (t : ℝ≥0) => B j t ω) P' ∧
      CouplingConverges M.P P'
        (fun n ω t => Fin.append (Fin.append (M.Ahat n ω t) (M.Shat n ω t)) (M.Rhat n ω t))
        (fun ω t j => Fin.append (Fin.append (fun i => Real.sqrt (M.lam i * M.cU2 i))
            (fun i => Real.sqrt (M.mu i))) (fun i => Real.sqrt (M.theta i)) j *
          B j t.toNNReal ω) := by
  let : IsProbabilityMeasure M.P := M.isProb
  let : M.P.IsComplete := M.complete
  obtain ⟨Λ,mΛ,P,B,hP,hB,hBc,hBm,hInd⟩ := finite_family_independent_continuous_brownian (k+k+k)
  letI := mΛ
  letI : IsProbabilityMeasure P := hP
  refine ⟨Λ,mΛ,P,B,hP,hB,hInd,?_⟩
  let X (n : ℕ) (ω : Ω) (t : ℝ) :=
    Fin.append (Fin.append (M.Ahat n ω t) (M.Shat n ω t)) (M.Rhat n ω t)
  let c := Fin.append (Fin.append (fun i => Real.sqrt (M.lam i * M.cU2 i))
    (fun i => Real.sqrt (M.mu i))) (fun i => Real.sqrt (M.theta i))
  let x (ω : Λ) (t : ℝ) (j : Fin (k+k+k)) := c j * B j t.toNNReal ω
  let π : (Fin k ⊕ Fin k) ⊕ Fin k ≃ Fin (k+k+k) :=
    (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv
  have heA (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :
      X n ω t (π (.inl (.inl i))) = M.Ahat n ω t i := by
    change X n ω t (Fin.castAdd k (Fin.castAdd k i)) = _
    simp only [X,Fin.append_left]
  have heS (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :
      X n ω t (π (.inl (.inr i))) = M.Shat n ω t i := by
    change X n ω t (Fin.castAdd k (Fin.natAdd k i)) = _
    simp only [X,Fin.append_left,Fin.append_right]
  have heR (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :
      X n ω t (π (.inr i)) = M.Rhat n ω t i := by
    change X n ω t (Fin.natAdd (k+k) i) = _
    simp only [X,Fin.append_right]
  have hJ (m : ℕ) (τ : Fin m → ℝ) (hτ : ∀ j, 0 ≤ τ j) :
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => x ω (τ j)) (fun _ => M.P) P :=
    queue_primitives_joint_finite_observation_limit M B hB hBc hInd τ hτ
  have hX (n : ℕ) (ω : Ω) (j : Fin (k+k+k)) : IsCadlag (fun t => X n ω t j) := by
    obtain ⟨i,rfl⟩ := π.surjective j
    rcases i with ((i | i) | i)
    · simpa only [heA] using (queue_centered_primitives_are_cadlag M n ω i).1
    · simpa only [heS] using (queue_centered_primitives_are_cadlag M n ω i).2.1
    · simpa only [heR] using (queue_centered_primitives_are_cadlag M n ω i).2.2
  have hXm (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : Measurable (fun ω => X n ω t) := by
    have h := (hJ 1 (fun _ => t) (fun _ => ht)).forall_aemeasurable n
    have hm : AEMeasurable (fun ω => X n ω t) M.P :=
      (measurable_pi_apply (0 : Fin 1)).comp_aemeasurable h
    exact hm.nullMeasurable.measurable_of_complete
  have hxc (ω : Λ) : Continuous (x ω) := by
    apply continuous_pi
    intro i
    exact ((hBc i ω).comp continuous_real_toNNReal).const_mul _
  have hxm (t : ℝ) : Measurable (fun ω => x ω t) :=
    measurable_pi_lambda _ (fun j => (hBm j t.toNNReal).const_mul _)
  have hMod (T : ℕ) :
      ∀ (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
        M.P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
          ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η := by
    apply finite_coordinate_modulus_controls_vector_modulus M.P X T
    intro j ε η hε hη
    obtain ⟨i,rfl⟩ := π.surjective j
    rcases i with ((i | i) | i)
    · obtain ⟨A,hA,δ,hδ,h⟩ := queue_arrival_norm_and_modulus_bounds M i
        (hB (π (.inl (.inl i)))) (hBc (π (.inl (.inl i)))) T (Nat.cast_nonneg _) ε η hε hη
      refine ⟨δ,hδ,?_⟩
      filter_upwards [h] with n hn
      refine (measure_mono ?_).trans hn
      rintro ω ⟨s,hs,t,ht,hst,hb⟩
      exact Or.inr ⟨s,hs,t,ht,hst,by simpa only [heA] using hb⟩
    · let N (ω : Ω) (t : ℝ) := M.S 1 i ω ((M.muN 1 i)⁻¹*t)
      have hN : IsPoissonProcess M.P N 1 := by
        have h := poisson_primitive_deterministic_clock_change (M.S_poisson 1 i)
          (M.muN 1 i)⁻¹ (inv_pos.2 (M.muN_pos 1 i))
        simpa only [mul_inv_cancel₀ (M.muN_pos 1 i).ne'] using h
      simpa only [heS,SystemSequence.Shat] using
        poisson_rows_centered_interval_modulus_bound (fun n => M.S n i) (fun n => M.muN n i)
          (fun n => M.S_poisson n i) (M.mu i) (M.mu_pos i).le (M.mu_lim i) N hN
          (hB (π (.inl (.inr i)))) (hBc (π (.inl (.inr i)))) T ε η hε hη
    · let N (ω : Ω) (t : ℝ) := M.S 1 i ω ((M.muN 1 i)⁻¹*t)
      have hN : IsPoissonProcess M.P N 1 := by
        have h := poisson_primitive_deterministic_clock_change (M.S_poisson 1 i)
          (M.muN 1 i)⁻¹ (inv_pos.2 (M.muN_pos 1 i))
        simpa only [mul_inv_cancel₀ (M.muN_pos 1 i).ne'] using h
      simpa only [heR,SystemSequence.Rhat] using
        poisson_rows_centered_interval_modulus_bound (fun n => M.R n i) (fun n => M.thetaN n i)
          (fun n => M.R_poisson n i) (M.theta i) (M.theta_nonneg i) (M.theta_lim i) N hN
          (hB (π (.inr i))) (hBc (π (.inr i))) T ε η hε hη
  exact functional_coupling_from_fdd_and_interval_modulus X x hX hXm
    (fun ω => (hxc ω).continuousOn) (fun t _ => hxm t) hJ hMod
