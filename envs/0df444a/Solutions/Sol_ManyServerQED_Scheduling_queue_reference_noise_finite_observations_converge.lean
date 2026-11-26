-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_reference_noise_finite_observations_converge
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:10:14.023396+00:00
-- url     : https://prove2.me/submissions/0252d342-06ec-4bf1-b28f-fafd8c0e1d7f

import Theorems.Thm_ManyServerQED_Scheduling_queue_primitives_joint_finite_observation_limit
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 1300000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k) {P' : Measure Ω'} [IsProbabilityMeasure P']
    (B : Fin (k+k+k) → ℝ≥0 → Ω' → ℝ)
    (hB : ∀ j, IsBrownianReal (B j) P') (hBc : ∀ j ω, Continuous (fun t => B j t ω))
    (hI : iIndepFun (fun j ω (t : ℝ≥0) => B j t ω) P')
    {m : ℕ} (τ : Fin m → ℝ≥0) :
    letI := M.isProb
    TendstoInDistribution
      (fun n ω j i => (M.Ahat n ω (τ j) i - M.Shat n ω (M.rho i*(τ j:ℝ)) i)/M.diffData.r i)
      atTop (fun ω j i =>
        (Real.sqrt (M.lam i*M.cU2 i)*B (Fin.castAdd k (Fin.castAdd k i)) (τ j) ω -
          Real.sqrt (M.mu i)*B (Fin.castAdd k (Fin.natAdd k i)) ((M.rho i).toNNReal * τ j) ω) /
          M.diffData.r i) (fun _ => M.P) P' := by
  letI : IsProbabilityMeasure M.P := M.isProb
  let U := (Fin m) ⊕ (Fin m × Fin k)
  let e : Fin (Fintype.card U) ≃ U := (Fintype.equivFin U).symm
  let t (u : U) : ℝ := Sum.elim (fun j => (τ j:ℝ)) (fun p => M.rho p.2*(τ p.1:ℝ)) u
  have hρ (i : Fin k) : 0 ≤ M.rho i := (div_pos (M.lam_pos i) (M.mu_pos i)).le
  have ht (j : Fin (Fintype.card U)) : 0 ≤ t (e j) := by
    rcases e j with j | ⟨j,i⟩
    · exact (τ j).2
    · exact mul_nonneg (hρ i) (τ j).2
  have h := queue_primitives_joint_finite_observation_limit M B hB hBc hI (t ∘ e) ht
  let A (i : Fin k) := Fin.castAdd k (Fin.castAdd k i)
  let S (i : Fin k) := Fin.castAdd k (Fin.natAdd k i)
  let l (z : Fin (Fintype.card U) → Fin (k+k+k) → ℝ) (j : Fin m) (i : Fin k) :=
    (z (e.symm (.inl j)) (A i) - z (e.symm (.inr (j,i))) (S i))/M.diffData.r i
  have hl : Continuous l := by
    unfold l
    fun_prop
  refine (h.continuous_comp hl).congr (fun n => Eventually.of_forall (fun ω => ?_))
    (Eventually.of_forall (fun ω => ?_))
  · funext j i
    simp only [Function.comp_apply,l,t,A,S,Equiv.apply_symm_apply,Sum.elim_inl,Sum.elim_inr,
      Fin.append_left,Fin.append_right]
  · funext j i
    simp only [Function.comp_apply,l,t,A,S,Equiv.apply_symm_apply,Sum.elim_inl,Sum.elim_inr,
      Fin.append_left,Fin.append_right,Real.toNNReal_coe,Real.toNNReal_mul (hρ i)]
