-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_joint_limit_path_identities
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:52:31.765947+00:00
-- url     : https://prove2.me/submissions/2ecc2611-d721-400f-9e5e-d86ebb4cfc1b

import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_coupled_drift_density
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_gap_identity_on_coupled_limit
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_coupling_limit_state_balance
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_row_integral_paths
import Theorems.Thm_ManyServerQED_Scheduling_coupled_real_accumulators_preserve_monotonicity
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
    ∃ b : ℝ≥0 → d.Ω' → Fin k → ℝ,
      Measurable (fun z : d.Ω' × ℝ≥0 => b z.2 z.1) ∧
      (∃ a : ℝ, 0 ≤ a ∧ ∀ ω t, ‖b t ω‖ ≤ a*(1+l1norm (d.state t ω))) ∧
      (∀ᵐ ω ∂d.Q, d.state 0 ω = x) ∧
      (∀ᵐ ω ∂d.Q, ∀ t : ℝ≥0,
        d.state t ω = x + (fun i => M.diffData.r i*d.noise t ω i) +
          ∫ s in (0:ℝ)..(t:ℝ), b s.toNNReal ω) ∧
      (∀ᵐ ω ∂d.Q, Monotone (fun t => d.runningCost t ω)) ∧
      (∀ᵐ ω ∂d.Q, Monotone (fun t => d.gap t ω)) ∧
      (∀ᵐ ω ∂d.Q, d.runningCost 0 ω = 0) ∧
      (∀ᵐ ω ∂d.Q, ∀ t : ℝ≥0, d.gap t ω = d.runningCost t ω +
        ∫ r in (0:ℝ)..(t:ℝ), Real.exp (-γ*r) *
          ((∑ i, b r.toNNReal ω i * grad f (d.state r.toNNReal ω) i) -
            hamiltonian M.diffData (costOfTilde Lt) (d.state r.toNNReal ω)
              (grad f (d.state r.toNNReal ω)))) := by

  let Z := queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ
  let ctl (n : ℕ) (hn : 1 ≤ n) := (hpol n hn).1.controlled
  let work (n : ℕ) (hn : 1 ≤ n) := (hpol n hn).2.2
  let scp (n : ℕ) (hn : 1 ≤ n) := (hpol n hn).1
  obtain ⟨a,ha,b,hBm,hB,hPrim,hRows⟩ :=
    queue_hjb_coupled_drift_density M Lt γ ϱ mL hA2 u0 hu0 f hHJB X Ψ X0 scp work s hs d
  have hGap := queue_hjb_gap_identity_on_coupled_limit M Lt γ ϱ mL hA2 u0 hu0 f hHJB X Ψ X0
    scp work s hs d a ha b hBm hB hPrim hRows
  obtain ⟨hInit,hDr0,hC0,hEq⟩ := queue_hjb_coupling_limit_state_balance M (costOfTilde Lt) γ
    X0 x hX0 u0 f X Ψ ctl work s hs d
  let b' (t : ℝ≥0) (ω : d.Ω') := b ω t
  have hMe : Measurable (fun z : d.Ω' × ℝ≥0 => b' z.2 z.1) :=
    hBm.comp (measurable_fst.prodMk measurable_snd.coe_nnreal_real)
  have hBd (ω : d.Ω') (t : ℝ≥0) : ‖b' t ω‖ ≤ a*(1+l1norm (d.state t ω)) := by
    simpa only [Real.toNNReal_coe,b',QueueHJBPathSubseq.state,l1norm] using hB ω t
  have hTranslate (ω : d.Ω') (t : ℝ≥0) :
      (∫ r in (0:ℝ)..(t:ℝ), b' r.toNNReal ω) = ∫ r in (0:ℝ)..(t:ℝ), b ω r := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0:ℝ) (t:ℝ) := (uIcc_of_le (show (0:ℝ) ≤ (t:ℝ) from t.2)) ▸ hr
    simp only [b',Real.coe_toNNReal _ hr'.1]
  have hEq' : ∀ᵐ ω ∂d.Q, ∀ t : ℝ≥0, d.state t ω =
      x+(fun i => M.diffData.r i*d.noise t ω i)+∫ r in (0:ℝ)..(t:ℝ), b' r.toNNReal ω := by
    filter_upwards [hEq,hDr0,hPrim] with ω hω h0 hP
    intro t
    rw [hTranslate,hP t,h0,sub_zero]
    exact hω t
  have hGap' : ∀ᵐ ω ∂d.Q, ∀ t : ℝ≥0, d.gap t ω = d.runningCost t ω +
      ∫ r in (0:ℝ)..(t:ℝ), Real.exp (-γ*r) *
        ((∑ i, b' r.toNNReal ω i*grad f (d.state r.toNNReal ω) i) -
          hamiltonian M.diffData (costOfTilde Lt) (d.state r.toNNReal ω)
            (grad f (d.state r.toNNReal ω))) := by
    filter_upwards [hGap] with ω h
    intro t
    rw [h t]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0:ℝ) (t:ℝ) := (uIcc_of_le (show (0:ℝ) ≤ (t:ℝ) from t.2)) ▸ hr
    simp only [b',Real.coe_toNNReal _ hr'.1]
  have hInt := (queue_hjb_row_integral_paths M Lt γ ϱ mL hA2 u0 hu0 f hHJB X Ψ X0 scp work).1
  have hMonoC : ∀ᵐ ω ∂d.Q, Monotone (fun t => d.runningCost t ω) := by
    let i : Fin (k+k+k+2) := Fin.natAdd (k+k+k) (0:Fin 2)
    apply coupled_real_accumulators_preserve_monotonicity d hs (fun z => z i) (continuous_apply i)
    filter_upwards [eventually_ge_atTop 1] with n hn
    intro ω
    simpa only [Z,queueHJBObservation,Fin.append_right,i,Matrix.cons_val_zero] using (hInt n hn ω).2.2.2.1
  have hMonoG : ∀ᵐ ω ∂d.Q, Monotone (fun t => d.gap t ω) := by
    let i : Fin (k+k+k+2) := Fin.natAdd (k+k+k) (1:Fin 2)
    apply coupled_real_accumulators_preserve_monotonicity d hs (fun z => z i) (continuous_apply i)
    filter_upwards [eventually_ge_atTop 1] with n hn
    intro ω
    have hOne : (1 : Fin 2) = Fin.succ (0 : Fin 1) := rfl
    simpa only [Z,queueHJBObservation,Fin.append_right,i,hOne,Matrix.cons_val_succ,Matrix.cons_val_zero] using (hInt n hn ω).2.2.2.2.1
  exact ⟨b',hMe,⟨a,ha.le,hBd⟩,hInit,hEq',hMonoC,hMonoG,hC0,hGap'⟩
