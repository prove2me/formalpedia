-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_subsequence_limit_paths
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:23:49.69584+00:00
-- url     : https://prove2.me/submissions/dff06266-c742-4b77-9f06-0171a57f4bf2

import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_joint_path_subsequence
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_joint_limit_filtered_brownian
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_joint_limit_path_identities
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_joint_limit_moments_and_cost
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


set_option maxHeartbeats 1500000 in
private theorem queue_hjb_gap_limit_of_uoc_zero {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (P : Measure Ω)
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop) (d : QueueHJBPathSubseq P Z s)
    (h : UocInProb P (fun n ω t => ![Z n ω t (Fin.natAdd (k+k+k) (1 : Fin 2))]) (fun _ => 0)) :
    ∀ T : ℝ≥0, ∀ᵐ ω ∂d.Q, d.gap T ω = 0 := by
  intro T
  let : IsProbabilityMeasure d.Q := d.isProb
  let i : Fin (k+k+k+2) := Fin.natAdd (k+k+k) (1 : Fin 2)
  obtain ⟨N,hN⟩ := eventually_atTop.1 d.row_law
  let j (n : ℕ) := n+N
  let q (n : ℕ) (ω : d.Ω') := d.row (j n) ω T i
  let q' (n : ℕ) (ω : Ω) := Z (s (d.r (j n))) ω T i
  let a (ω : d.Ω') := d.gap T ω
  have hJ : Tendsto j atTop atTop := tendsto_add_atTop_nat N
  let ev (p : ℝ≥0 → Fin (k+k+k+2) → ℝ) := p T i
  have hEv : Measurable ev := (measurable_pi_apply i).comp (measurable_pi_apply T)
  have hLaw (n : ℕ) : IdentDistrib (q n) (q' n) d.Q P :=
    (hN (j n) (by dsimp [j]; omega)).comp hEv
  have hAe : ∀ᵐ ω ∂d.Q, Tendsto (fun n => q n ω) atTop (𝓝 (a ω)) := by
    filter_upwards [d.convergence] with ω hω
    have hSup := (hω (T:ℝ) T.2).comp hJ
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [(tendsto_order.1 hSup).2 _ (ENNReal.ofReal_pos.2 hε)] with n hn
    have hs : |q n ω-a ω| ≤ ∑ l, |d.row (j n) ω T l-d.limit ω T l| :=
      Finset.single_le_sum (fun l _ => abs_nonneg (d.row (j n) ω T l-d.limit ω T l)) (Finset.mem_univ i)
    have hU : ENNReal.ofReal |q n ω-a ω| ≤ supDist (d.row (j n) ω) (d.limit ω) (T:ℝ) :=
      (ENNReal.ofReal_le_ofReal hs).trans (le_iSup_of_le (T:ℝ) (le_iSup_of_le ⟨T.2,le_rfl⟩ le_rfl))
    rw [Real.dist_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).1 (hU.trans_lt hn)
  have hQ : TendstoInMeasure d.Q q atTop a :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hLaw n).aemeasurable_fst.aestronglyMeasurable) hAe
  have hq0 : TendstoInMeasure d.Q q atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hT := (h (T:ℝ) T.2 ε hε).comp (hs.comp (d.r_cofinal.comp hJ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
      (Eventually.of_forall (fun _ => zero_le)) (Eventually.of_forall fun n => ?_)
    let A : Set ℝ := {x | ε ≤ |x|}
    have hA : MeasurableSet A := measurableSet_le measurable_const measurable_id.abs
    have heq : d.Q (q n ⁻¹' A) = P (q' n ⁻¹' A) := by
      have h := congrArg (fun m : Measure ℝ => m A) (hLaw n).map_eq
      rwa [Measure.map_apply_of_aemeasurable (hLaw n).aemeasurable_fst hA,
        Measure.map_apply_of_aemeasurable (hLaw n).aemeasurable_snd hA] at h
    simp only [sub_zero,Real.norm_eq_abs]
    change d.Q (q n ⁻¹' A) ≤ _
    rw [heq]
    apply measure_mono
    intro ω hw
    have hAt : ENNReal.ofReal |q' n ω| ≤ supDist
        (fun t => ![Z (s (d.r (j n))) ω t i]) (fun _ => 0) (T:ℝ) := by
      apply le_iSup_of_le (T:ℝ)
      apply le_iSup_of_le (show (T:ℝ) ∈ Icc (0:ℝ) (T:ℝ) from ⟨T.2,le_rfl⟩)
      simp [q']
    exact (ENNReal.ofReal_le_ofReal hw).trans hAt
  exact tendstoInMeasure_ae_unique hQ hq0

set_option maxHeartbeats 1300000 in
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
    :
    ∀ s : ℕ → ℕ, Tendsto s atTop atTop →
      ∃ r : ℕ → ℕ, Tendsto r atTop atTop ∧
      ∃ d : HJBCostLimit M.diffData (costOfTilde Lt) γ f x,
        (∀ T : ℕ, Tendsto (fun j =>
          ∫⁻ ω, ∫⁻ t in Set.Ioc (0:ℝ) (T:ℝ),
            ENNReal.ofReal (Real.exp (-γ*t) *
              costOfTilde Lt (M.Xhat (s (r j)) (X (s (r j))) ω t)
                (uProc (s (r j)) u0 (X (s (r j))) (Ψ (s (r j))) ω t)) ∂volume ∂M.P)
          atTop (𝓝 (ENNReal.ofReal (∫ ω, d.cost T ω ∂d.P)))) ∧
        (∃ a : ℝ, 0 ≤ a ∧ ∀ ω t, ‖d.b t ω‖ ≤ a*(1+l1norm (d.X t ω))) ∧
        (∀ (T : ℝ≥0) (q : ℕ), ∃ V : d.Ω → ℝ, Integrable V d.P ∧
          ∀ᵐ ω ∂d.P, ∀ t ≤ T, l1norm (d.X t ω)^q ≤ V ω) ∧
        (UocInProb M.P
      (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) *
        (∑ i, drift M.diffData (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) i *
            grad f (M.Xhat n (X n) ω s) i +
          costOfTilde Lt (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) -
          hamiltonian M.diffData (costOfTilde Lt) (M.Xhat n (X n) ω s)
            (grad f (M.Xhat n (X n) ω s)))])
      (fun _ => 0) → ∀ T : ℕ, ∀ᵐ ω ∂d.P, d.gap T ω = 0) := by 
  intro s hs
  obtain ⟨d⟩ := queue_hjb_joint_path_subsequence M Lt ϱ mL mU γ hA2 hA3 hγ
    u0 hu0 X0 x hX0 X Ψ hpol f hf hHJB s hs
  obtain ⟨F,hW,hXad⟩ := queue_hjb_joint_limit_filtered_brownian M Lt ϱ mL mU γ hA2 hA3 hγ
    u0 hu0 X0 x hX0 X Ψ hpol f hf hHJB s hs d
  obtain ⟨b,hbm,hLinear,hX0',hState,hCostMono,hGapMono,hCost0,hGapEq⟩ :=
    queue_hjb_joint_limit_path_identities M Lt ϱ mL mU γ hA2 hA3 hγ
      u0 hu0 X0 x hX0 X Ψ hpol f hf hHJB s hs d
  obtain ⟨hMoment,hSup,hCostI,hCostConv⟩ :=
    queue_hjb_joint_limit_moments_and_cost M Lt ϱ mL mU γ hA2 hA3 hγ
      u0 hu0 X0 x hX0 X Ψ hpol f hf hHJB s hs d F hW
  have hCont (ω : d.Ω') : Continuous (fun t : ℝ≥0 => d.limit ω t) :=
    (d.limit_cont ω).comp_continuous continuous_subtype_val (fun t => t.2)
  have hXc (ω : d.Ω') : Continuous (fun t => d.state t ω) :=
    continuous_pi (fun i => (continuous_apply _).comp (hCont ω))
  have hCc (ω : d.Ω') : Continuous (fun t => d.runningCost t ω) :=
    (continuous_apply _).comp (hCont ω)
  have hGc (ω : d.Ω') : Continuous (fun t => d.gap t ω) :=
    (continuous_apply _).comp (hCont ω)
  have hGm (t : ℝ≥0) : Measurable (d.gap t) :=
    (measurable_pi_apply _).comp (d.limit_meas t)
  have hbb (ω : d.Ω') (T : ℝ≥0) : ∃ c : ℝ, ∀ t ∈ Icc 0 T, ‖b t ω‖ ≤ c := by
    obtain ⟨a,ha,hb⟩ := hLinear
    have hc : Continuous (fun t : ℝ≥0 => l1norm (d.state t ω)) := by
      unfold l1norm
      apply continuous_finset_sum
      intro i _
      exact ((continuous_apply i).comp (hXc ω)).abs
    obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ≥0) T)).exists_bound_of_continuousOn
      hc.continuousOn
    exact ⟨a*(1+C),fun t ht => (hb ω t).trans
      (mul_le_mul_of_nonneg_left (add_le_add_right ((le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs] using hC t ht)) 1) ha)⟩
  let out : HJBCostLimit M.diffData (costOfTilde Lt) γ f x :=
    { Ω := d.Ω'
      mΩ := d.mΩ'
      P := d.Q
      isProb := d.isProb
      F := F
      W := d.noise
      W_bm := hW
      X := d.state
      X_cont := hXc
      X_adapted := hXad
      X_zero := hX0'
      X_moment := hMoment
      b := b
      b_meas := hbm
      b_bound := hbb
      state_eq := hState
      cost := d.runningCost
      gap := d.gap
      cost_cont := hCc
      gap_cont := hGc
      cost_integrable := hCostI
      gap_meas := hGm
      cost_increases := hCostMono
      gap_increases := hGapMono
      cost_zero := hCost0
      gap_eq := hGapEq }
  refine ⟨d.r,d.r_cofinal,out,hCostConv,hLinear,hSup,?_⟩
  intro h49 T
  exact queue_hjb_gap_limit_of_uoc_zero M.P hs d (by
    simpa only [queueHJBObservation,Fin.append_right,Matrix.cons_val_one,Matrix.cons_val_zero] using h49) (T:ℝ≥0)
