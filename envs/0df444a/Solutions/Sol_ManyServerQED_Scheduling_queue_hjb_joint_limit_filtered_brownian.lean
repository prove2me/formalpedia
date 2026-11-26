-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_joint_limit_filtered_brownian
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:41:36.348078+00:00
-- url     : https://prove2.me/submissions/44b5f7f4-f10e-42bc-a8f6-b4c954612d83

import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_integrands_on_bounded_state_sets
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_coupled_paths_have_joint_observation_limits
import Theorems.Thm_ManyServerQED_Scheduling_finite_family_independent_continuous_brownian
import Theorems.Thm_ManyServerQED_Scheduling_queue_reference_noise_is_standard_brownian
import Theorems.Thm_ManyServerQED_Scheduling_joint_observation_finite_laws_give_filtered_brownian
import Theorems.Thm_ManyServerQED_Scheduling_queue_reference_noise_finite_observations_converge
import Theorems.Thm_ManyServerQED_Scheduling_queue_effective_noise_reference_and_future_approximations
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_measurable_in_queue_past
import Theorems.Thm_ManyServerQED_Scheduling_shifted_queue_noise_measurable_in_future
import Theorems.Thm_ManyServerQED_Scheduling_independence_under_negligible_weak_limit_perturbations
import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_HJBCostLimit
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy



set_option maxHeartbeats 1100000 in
private theorem nested_probability_errors {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {I J : Type*} [Fintype I] [Fintype J] (D : ℕ → Ω → I → J → ℝ)
    (h : ∀ i j ε, 0 < ε → Tendsto (fun n => P {ω | ε ≤ |D n ω i j|}) atTop (𝓝 0)) :
    TendstoInMeasure P D atTop (fun _ => 0) := by
  classical
  apply tendstoInMeasure_iff_norm.2
  intro ε hε
  let H (ij : I × J) (n : ℕ) := P {ω | ε/2 ≤ |D n ω ij.1 ij.2|}
  have hSum : Tendsto (fun n => ∑ ij, H ij n) atTop (𝓝 0) := by
    simpa using (tendsto_finsetSum Finset.univ (fun (ij : I × J) _ => h ij.1 ij.2 (ε/2) (half_pos hε)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSum
    (fun _ => bot_le) fun n => ?_
  simp only [sub_zero]
  let B (ij : I × J) : Set Ω := {ω | ε/2 ≤ |D n ω ij.1 ij.2|}
  have hB : P (⋃ ij, B ij) ≤ ∑ ij, H ij n := by
    simpa only [tsum_fintype,H,B] using (measure_iUnion_le (μ := P) B)
  refine (measure_mono ?_).trans hB
  intro ω hw
  by_contra ha
  have hBound : ‖D n ω‖ ≤ ε/2 := (pi_norm_le_iff_of_nonneg (half_pos hε).le).2 fun i =>
    (pi_norm_le_iff_of_nonneg (half_pos hε).le).2 fun j => by
      rw [Real.norm_eq_abs]
      exact (lt_of_not_ge (fun h' => ha (mem_iUnion.2 ⟨(i,j),h'⟩))).le
  have hw' : ε ≤ ‖D n ω‖ := hw
  linarith

set_option maxHeartbeats 2400000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hpol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n))
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f)
    (hHJB : IsHJBSolution M.diffData (costOfTilde Lt) γ f)

    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (d : QueueHJBPathSubseq M.P (queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ) s) :
    ∃ F : Filtration ℝ≥0 d.mΩ', IsStdFBrownian d.Q F d.noise ∧
      ∀ t, Measurable[F t] (d.state t) := by

  classical
  letI : IsProbabilityMeasure M.P := M.isProb
  letI : IsProbabilityMeasure d.Q := d.isProb
  let Z := queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ
  let m := k+k+k+2
  let jW (i : Fin k) : Fin m := Fin.castAdd 2 (Fin.castAdd k (Fin.natAdd k i))
  let noise (n : ℕ) (ω : Ω) (t : ℝ≥0) (i : Fin k) := Z n ω t (jW i)
  let ctl (n : ℕ) (h : 1 ≤ n) := (hpol n h).1.controlled
  let work (n : ℕ) (h : 1 ≤ n) := (hpol n h).2.2
  obtain ⟨hL,_,_,_,_,_⟩ := queue_hjb_integrands_on_bounded_state_sets M.diffData Lt γ ϱ mL hA2 f hHJB
  obtain ⟨N,hFD⟩ := queue_hjb_coupled_paths_have_joint_observation_limits d
  have hfc : Tendsto (fun j => s (d.r (j+N))) atTop atTop :=
    hs.comp (d.r_cofinal.comp (tendsto_add_atTop_nat N))
  obtain ⟨K,hK⟩ := eventually_atTop.1 (hfc.eventually (eventually_ge_atTop 1))
  let n (j : ℕ) := s (d.r ((j+K)+N))
  have hn (j : ℕ) : 1 ≤ n j := hK (j+K) (by omega)
  have hnc : Tendsto n atTop atTop := hfc.comp (tendsto_add_atTop_nat K)
  have hF (a : ℕ) (τ : Fin a → ℝ≥0) :
      TendstoInDistribution (fun j ω l => Z (n j) ω (τ l)) atTop
        (fun ω l => d.limit ω (τ l)) (fun _ => M.P) d.Q := by
    have h := hFD a τ
    exact ⟨fun j => h.forall_aemeasurable (j+K),h.aemeasurable_limit,
      h.tendsto.comp (tendsto_add_atTop_nat K)⟩
  obtain ⟨Λ,mΛ,P,B,hP,hB,hBc,hBm,hI⟩ :=
    finite_family_independent_continuous_brownian (k+k+k)
  letI := mΛ
  letI : IsProbabilityMeasure P := hP
  let V (t : ℝ≥0) (ω : Λ) (i : Fin k) :=
    (Real.sqrt (M.lam i*M.cU2 i)*B (Fin.castAdd k (Fin.castAdd k i)) t ω -
      Real.sqrt (M.mu i)*B (Fin.castAdd k (Fin.natAdd k i)) ((M.rho i).toNNReal*t) ω)/M.diffData.r i
  have hVm (t : ℝ≥0) : Measurable (V t) :=
    measurable_pi_lambda _ (fun i => ((hBm _ _).const_mul _ |>.sub ((hBm _ _).const_mul _)).div_const _)
  obtain ⟨hVB,hVi⟩ := queue_reference_noise_is_standard_brownian M B hB hBm hI
  refine joint_observation_finite_laws_give_filtered_brownian d V hVB hVi hVm ?_ ?_
  · intro a τ
    let l (z : Fin a → Fin m → ℝ) (q : Fin a) (i : Fin k) := z q (jW i)
    have hl : Continuous l := continuous_pi (fun q => continuous_pi (fun i =>
      (continuous_apply (jW i)).comp (continuous_apply q)))
    have hc := (hF a τ).continuous_comp hl
    let ref (l : ℕ) (ω : Ω) (q : Fin a) (i : Fin k) :=
      (M.Ahat (n l) ω (τ q) i - M.Shat (n l) ω (M.rho i*(τ q:ℝ)) i)/M.diffData.r i
    let y (l : ℕ) (ω : Ω) (q : Fin a) (i : Fin k) := noise (n l) ω (τ q) i
    let w (ω : Λ) (q : Fin a) := V (τ q) ω
    let w' (ω : d.Ω') (q : Fin a) := d.noise (τ q) ω
    have hC : TendstoInDistribution y atTop w' (fun _ => M.P) d.Q := hc
    have hh := queue_reference_noise_finite_observations_converge M B hB hBc hI τ
    have hRef : TendstoInDistribution ref atTop w (fun _ => M.P) P :=
      ⟨fun l => hh.forall_aemeasurable (n l),hh.aemeasurable_limit,hh.tendsto.comp hnc⟩
    have hErr : TendstoInMeasure M.P (y - ref) atTop 0 := by
      apply nested_probability_errors M.P
      intro j i ε hε
      have h := (queue_effective_noise_reference_and_future_approximations M mL mU hA3
        X0 x hX0 X Ψ ctl work i 0 le_rfl (τ j) (τ j).2 ε hε).1.comp hnc
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
        (fun _ => bot_le) fun l => measure_mono ?_
      intro ω hω
      refine ⟨τ j,⟨(τ j).2,le_rfl⟩,?_⟩
      change ε ≤ |y l ω j i - ref l ω j i| at hω
      simpa only [y,noise,Z,queueHJBObservation,jW,Fin.append_left,Fin.append_right,ref] using hω
    have hV := tendstoInDistribution_of_tendstoInMeasure_sub y w hRef hErr hC.forall_aemeasurable
    exact ⟨hC.aemeasurable_limit,hV.aemeasurable_limit,
      congrArg (fun μ : ProbabilityMeasure (Fin a → Fin k → ℝ) =>
        (μ : Measure (Fin a → Fin k → ℝ))) (tendsto_nhds_unique hC.tendsto hV.tendsto)⟩
  · intro t a b p q hp
    let τ := Fin.append p (Fin.cons t (fun j : Fin b => t+q j))
    let l (z : Fin (a+(b+1)) → Fin m → ℝ) :=
      ((fun j : Fin a => z (Fin.castAdd (b+1) j)),
       (fun j : Fin b => fun i : Fin k =>
         z (Fin.natAdd a j.succ) (jW i)-z (Fin.natAdd a (0:Fin (b+1))) (jW i)))
    have hl : Continuous l := by
      unfold l
      fun_prop
    let E (j : ℕ) (ω : Ω) (u : Fin a) := Z (n j) ω (p u)
    let I (j : ℕ) (ω : Ω) (u : Fin b) := noise (n j) ω (t+q u)-noise (n j) ω t
    let Y (j : ℕ) (ω : Ω) (u : Fin b) (i : Fin k) :=
      ((M.Ahat (n j) ω (M.nextArrival (n j) i ω t+(q u:ℝ)) i -
        M.Ahat (n j) ω (M.nextArrival (n j) i ω t) i) -
        (M.Shat (n j) ω (busyTime (Ψ (n j)) ω i t/(n j:ℝ)+M.rho i*(q u:ℝ)) i -
          M.Shat (n j) ω (busyTime (Ψ (n j)) ω i t/(n j:ℝ)) i))/M.diffData.r i
    let e (ω : d.Ω') (u : Fin a) := d.limit ω (p u)
    let v (ω : d.Ω') (u : Fin b) := d.noise (t+q u) ω-d.noise t ω
    have hT : TendstoInDistribution (fun j ω => (E j ω,I j ω)) atTop
        (fun ω => (e ω,v ω)) (fun _ => M.P) d.Q := by
      refine ((hF _ τ).continuous_comp hl).congr
        (fun j => Eventually.of_forall (fun ω => ?_)) (Eventually.of_forall (fun ω => ?_))
      · apply Prod.ext
        · funext u
          simp only [Function.comp_apply,l,E,τ,Fin.append_left]
        · funext u i
          simp only [Function.comp_apply,l,I,τ,noise,Pi.sub_apply,Fin.append_right,
            Fin.cons_succ,Fin.cons_zero]
      · apply Prod.ext
        · funext u
          simp only [Function.comp_apply,l,e,τ,Fin.append_left]
        · funext u i
          simp only [Function.comp_apply,l,v,τ,Pi.sub_apply,Fin.append_right,
            Fin.cons_succ,Fin.cons_zero,QueueHJBPathSubseq.noise,jW]
    have hE (j : ℕ) : @Measurable Ω (Fin a → Fin m → ℝ) (M.pastInfo (n j) (X (n j)) (Ψ (n j)) t) _ (E j) :=
      @measurable_pi_lambda Ω (Fin a) (fun _ => Fin m → ℝ)
        (M.pastInfo (n j) (X (n j)) (Ψ (n j)) t) _ (E j) (fun u =>
        queue_hjb_observation_measurable_in_queue_past M (costOfTilde Lt) γ hL u0 f hHJB
          (n j) (hn j) (X0 (n j)) X Ψ (hpol (n j) (hn j)).1 t (p u) (hp u))
    have hY (j : ℕ) (u : Fin b) (i : Fin k) :=
      shifted_queue_noise_measurable_in_future M (n j) (hn j) (X0 (n j)) (X (n j)) (Ψ (n j))
        (hpol (n j) (hn j)).1 i t (q u)
    have hYm (j : ℕ) : AEMeasurable (Y j) M.P :=
      (measurable_pi_lambda _ fun u => measurable_pi_lambda _ fun i => (hY j u i).1).aemeasurable
    have hYi (j : ℕ) : IndepFun (E j) (Y j) M.P := by
      have hIn := (hpol (n j) (hn j)).2.1.indep t t.2
      let G := M.futureInfo (n j) (X (n j)) (Ψ (n j)) t
      have hYm : @Measurable Ω (Fin b → Fin k → ℝ) G _ (Y j) :=
        @measurable_pi_lambda Ω (Fin b) (fun _ => Fin k → ℝ) G _ _ (fun u =>
          @measurable_pi_lambda Ω (Fin k) (fun _ => ℝ) G _ _ (fun i => (hY j u i).2))
      exact (IndepFun_iff_Indep _ _ _).2
        (indep_of_indep_of_le hIn (hE j).comap_le hYm.comap_le)
    have hErr : TendstoInMeasure M.P (fun j ω => Y j ω-I j ω) atTop (fun _ => 0) := by
      apply nested_probability_errors M.P
      intro j i ε hε
      have h := (queue_effective_noise_reference_and_future_approximations M mL mU hA3
        X0 x hX0 X Ψ ctl work i t t.2 ((t+q j:ℝ≥0):ℝ)
        (by exact_mod_cast le_add_of_nonneg_right (show 0 ≤ q j from bot_le)) ε hε).2.comp hnc
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
        (fun _ => bot_le) fun l => measure_mono ?_
      intro ω hω
      refine ⟨((t+q j:ℝ≥0):ℝ),⟨by exact_mod_cast le_add_of_nonneg_right (show 0 ≤ q j from bot_le),le_rfl⟩,?_⟩
      change ε ≤ |Y l ω j i-I l ω j i| at hω
      simpa only [Y,I,Pi.sub_apply,noise,Z,jW,queueHJBObservation,Fin.append_left,
        Fin.append_right,NNReal.coe_add,add_sub_cancel_left] using hω
    exact independence_under_negligible_weak_limit_perturbations E I Y e v hT hYm hErr
      (Eventually.of_forall hYi)
