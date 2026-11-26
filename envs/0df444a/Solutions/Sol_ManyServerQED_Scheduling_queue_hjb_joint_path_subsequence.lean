-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_joint_path_subsequence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:44:21.061227+00:00
-- url     : https://prove2.me/submissions/22f4c20c-2d3a-4baf-82d7-8441a5bddf3e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_row_integral_paths
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_integrands_on_bounded_state_sets
import Theorems.Thm_ManyServerQED_Scheduling_queue_past_information_le_ambient
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_measurable_in_queue_past
import Theorems.Thm_ManyServerQED_Scheduling_controlled_queue_state_and_effective_noise_are_cadlag
import Theorems.Thm_ManyServerQED_Scheduling_joint_queue_hjb_observation_asymptotic_interval_modulus
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_at_zero
import Theorems.Thm_ManyServerQED_Scheduling_interval_modulus_and_initial_bound_give_compact_containment
import Theorems.Thm_ManyServerQED_Scheduling_finite_dimensional_cadlag_processes_have_compact_subsequence_coupling
import Theorems.Thm_ManyServerQED_Scheduling_continuous_limit_can_be_realized_on_a_path_coupling
import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_HJBCostLimit
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy



open Set
private theorem cadlag_of_continuousOn {f : ℝ → ℝ} (h : ContinuousOn f (Ici (0:ℝ))) :
    IsCadlag f := by
  refine ⟨fun t ht => (h t ht).mono (fun s hs => ht.trans hs),fun t ht => ⟨f t,?_⟩⟩
  have ht' : Ici (0:ℝ) ∈ 𝓝 t := Ici_mem_nhds ht
  exact ((h t ht.le).continuousAt ht').tendsto.mono_left nhdsWithin_le_nhds


set_option maxHeartbeats 2500000 in
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

    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop) :
    Nonempty (QueueHJBPathSubseq M.P (queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ) s) := by

  letI : IsProbabilityMeasure M.P := M.isProb
  let L := costOfTilde Lt
  let Z := queueHJBObservation M L γ u0 f X Ψ
  let m := k+k+k+2
  let ctl (n : ℕ) (hn : 1 ≤ n) := (hpol n hn).1.controlled
  let work (n : ℕ) (hn : 1 ≤ n) := (hpol n hn).2.2
  have hH := queue_hjb_row_integral_paths M Lt γ ϱ mL hA2 u0 hu0 f hHJB
    X Ψ X0 (fun n hn => (hpol n hn).1) work
  obtain ⟨hLc,_,_,_,_,_⟩ :=
    queue_hjb_integrands_on_bounded_state_sets M.diffData Lt γ ϱ mL hA2 f hHJB
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hs.eventually (eventually_ge_atTop 1))
  let c (j : ℕ) := s (j+N)
  have hc (j : ℕ) : 1 ≤ c j := hN (j+N) (by omega)
  have hCof : Tendsto c atTop atTop := hs.comp (tendsto_add_atTop_nat N)
  let U (j : ℕ) := Z (c j)
  have hUm (j : ℕ) (t : ℝ) (ht : 0 ≤ t) : Measurable (fun ω => U j ω t) := by
    let t' : ℝ≥0 := ⟨t,ht⟩
    have hLe := queue_past_information_le_ambient M (c j) (X0 (c j))
      (X (c j)) (Ψ (c j)) (hpol (c j) (hc j)).1 t'
    exact (queue_hjb_observation_measurable_in_queue_past M L γ hLc u0 f hHJB
      (c j) (hc j) (X0 (c j)) X Ψ (hpol (c j) (hc j)).1 t' t' le_rfl).mono hLe le_rfl
  have hUc (j : ℕ) (ω : Ω) (i : Fin m) : IsCadlag (fun t => U j ω t i) := by
    let n := c j
    have hn := hc j
    have hIt := hH.1 n hn ω
    cases i using Fin.addCases with
    | right i =>
      fin_cases i
      · simpa only [U,Z,queueHJBObservation,Fin.append_right,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using
          cadlag_of_continuousOn hIt.2.1
      · simpa only [U,Z,queueHJBObservation,Fin.append_right,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using
          cadlag_of_continuousOn hIt.2.2.1
    | left i =>
      cases i using Fin.addCases with
      | right i =>
        simpa only [U,Z,queueHJBObservation,Fin.append_left,Fin.append_right] using
          cadlag_of_continuousOn (hIt.1 i)
      | left i =>
        cases i using Fin.addCases with
        | left i =>
          simpa only [U,Z,queueHJBObservation,Fin.append_left] using
            (controlled_queue_state_and_effective_noise_are_cadlag M n hn (X0 n) (X n) (Ψ n) (ctl n hn) ω i).1
        | right i =>
          simpa only [U,Z,queueHJBObservation,Fin.append_left,Fin.append_right] using
            (controlled_queue_state_and_effective_noise_are_cadlag M n hn (X0 n) (X n) (Ψ n) (ctl n hn) ω i).2
  have hMod (T : ℕ) (ε η : ℝ) (he : 0 < ε) (hη : 0 < η) :
      ∃ δ > 0, ∀ᶠ j in atTop, M.P {ω | ∃ p ∈ Icc (0:ℝ) (T:ℝ), ∃ q ∈ Icc (0:ℝ) (T:ℝ),
        |p-q| ≤ δ ∧ ε ≤ ‖U j ω p-U j ω q‖} ≤ ENNReal.ofReal η := by
    obtain ⟨δ,hδ,h⟩ := joint_queue_hjb_observation_asymptotic_interval_modulus M Lt ϱ mL mU γ
      hA2 hA3 u0 hu0 X0 x hX0 X Ψ hpol f hHJB T ε η he hη
    exact ⟨δ,hδ,hCof.eventually h⟩
  let emb (z : Fin k → ℝ) : Fin m → ℝ :=
    Fin.append (Fin.append (Fin.append z 0) 0) ![0,0]
  have hEmb : Continuous emb := by
    apply continuous_pi
    intro i
    cases i using Fin.addCases with
    | right j => simpa only [emb,Fin.append_right] using
        (continuous_const : Continuous (fun _ : Fin k → ℝ => (![0,0] : Fin 2 → ℝ) j))
    | left j =>
      cases j using Fin.addCases with
      | right j => simpa only [emb,Fin.append_left,Fin.append_right,Pi.zero_apply] using
          (continuous_const : Continuous (fun _ : Fin k → ℝ => (0:ℝ)))
      | left j =>
        cases j using Fin.addCases with
        | right j => simpa only [emb,Fin.append_left,Fin.append_right,Pi.zero_apply] using
            (continuous_const : Continuous (fun _ : Fin k → ℝ => (0:ℝ)))
        | left j => simpa only [emb,Fin.append_left] using (continuous_apply j)
  let C := ‖emb x‖+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have h0 : ∀ᶠ j in atTop, ∀ ω, ‖U j ω 0‖ ≤ C := by
    have h := hEmb.continuousAt.tendsto.comp (hX0.comp hCof)
    filter_upwards [Metric.tendsto_nhds.1 h 1 zero_lt_one] with j hj
    intro ω
    change ‖Z (c j) ω 0‖ ≤ C
    rw [show Z (c j) ω 0 = emb (M.Xhat0 (c j) (X0 (c j))) from
      queue_hjb_observation_at_zero M L γ u0 f X Ψ X0 (c j) (ctl (c j) (hc j)) ω]
    have hD := (norm_add_le (emb (M.Xhat0 (c j) (X0 (c j)))-emb x) (emb x))
    rw [sub_add_cancel] at hD
    simp only [dist_eq_norm,Function.comp_apply] at hj
    dsimp [C]
    linarith
  have hB (T : ℕ) (η : ℝ) (hη : 0 < η) : ∃ A ≥ (0:ℝ), ∀ᶠ j in atTop,
      M.P {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), A < ‖U j ω t‖} ≤ ENNReal.ofReal η :=
    interval_modulus_and_initial_bound_give_compact_containment M.P U T (Nat.cast_nonneg _) C hC h0
      (fun η hη => hMod T 1 η zero_lt_one hη) η hη
  obtain ⟨u,hu,Λ,mΛ,P,v,hP,hv,_,hK⟩ :=
    finite_dimensional_cadlag_processes_have_compact_subsequence_coupling U hUc hUm hB hMod
  letI := mΛ
  obtain ⟨Ω',mΩ',Q,Y,V,hQ,hLaw,_,hY,hV,hVm,hConv⟩ :=
    continuous_limit_can_be_realized_on_a_path_coupling M.P P (fun j => U (u j)) v hv hK
  letI := mΩ'
  exact ⟨{
    Ω' := Ω'
    mΩ' := mΩ'
    Q := Q
    isProb := hQ
    r := fun j => u j+N
    r_cofinal := (tendsto_add_atTop_nat N).comp hu.tendsto_atTop
    row := Y
    limit := V
    row_law := hLaw
    row_cadlag := hY
    limit_meas := hVm
    limit_cont := hV
    convergence := hConv }⟩
