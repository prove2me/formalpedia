-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_joint_limit_moments_and_cost
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:47:49.362679+00:00
-- url     : https://prove2.me/submissions/492c5dca-8182-40f5-8bf1-40b024000957

import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_rows_are_cadlag
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_state_growth_on_path_coupling
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_moments_from_brownian_growth
import Theorems.Thm_ManyServerQED_Scheduling_queue_finite_horizon_cost_uniform_moment
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_row_integral_paths
import Theorems.Thm_ManyServerQED_Scheduling_coupled_accumulated_cost_expectations_converge
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
    (d : QueueHJBPathSubseq M.P (queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ) s) (F : Filtration ℝ≥0 d.mΩ') (hW : IsStdFBrownian d.Q F d.noise) :
    (∀ p : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ j : ℕ, ∀ t : ℝ≥0,
      Integrable (fun ω => l1norm (d.state t ω)^p) d.Q ∧
      (∫ ω, l1norm (d.state t ω)^p ∂d.Q) ≤ c*(1+(t:ℝ)^j)) ∧
    (∀ (T : ℝ≥0) (q : ℕ), ∃ V : d.Ω' → ℝ, Integrable V d.Q ∧
      ∀ᵐ ω ∂d.Q, ∀ t ≤ T, l1norm (d.state t ω)^q ≤ V ω) ∧
    (∀ t, Integrable (d.runningCost t) d.Q) ∧
    (∀ T : ℕ, Tendsto (fun j =>
      ∫⁻ ω, ∫⁻ t in Set.Ioc (0:ℝ) (T:ℝ),
        ENNReal.ofReal (Real.exp (-γ*t) *
          costOfTilde Lt (M.Xhat (s (d.r j)) (X (s (d.r j))) ω t)
            (uProc (s (d.r j)) u0 (X (s (d.r j))) (Ψ (s (d.r j))) ω t))
        ∂volume ∂M.P) atTop (𝓝 (ENNReal.ofReal (∫ ω, d.runningCost T ω ∂d.Q)))) := by

  let C (n : ℕ) (hn : 1 ≤ n) := (hpol n hn).1.controlled
  let W (n : ℕ) (hn : 1 ≤ n) := (hpol n hn).2.2
  have hRows := queue_hjb_observation_rows_are_cadlag M Lt γ ϱ mL hA2 u0 hu0 f hHJB
    X Ψ X0 (fun n hn => (hpol n hn).1) W
  obtain ⟨a,ha,hG⟩ := queue_hjb_state_growth_on_path_coupling M (costOfTilde Lt) γ X0 x
    hX0 u0 f X Ψ C W s hs d ((eventually_ge_atTop 1).mono (fun n hn => hRows n hn))
  obtain ⟨hState,hDom⟩ := queue_hjb_moments_from_brownian_growth d F hW M.diffData.r
    M.diffData.r_pos a ha hG
  refine ⟨hState,hDom,?_⟩
  obtain ⟨p,hp,hM⟩ := queue_finite_horizon_cost_uniform_moment M Lt ϱ mL mU γ
    hA2 hA3 hγ u0 hu0 X0 x hX0 X Ψ hpol
  have hInt := (queue_hjb_row_integral_paths M Lt γ ϱ mL hA2 u0 hu0 f hHJB X Ψ X0
    (fun n hn => (hpol n hn).1) W).1
  have hCost (T : ℝ≥0) :
      Integrable (d.runningCost T) d.Q ∧
      Tendsto (fun j =>
        ∫⁻ ω, ∫⁻ t in Set.Ioc (0:ℝ) (T:ℝ),
          ENNReal.ofReal (Real.exp (-γ*t) *
          costOfTilde Lt (M.Xhat (s (d.r j)) (X (s (d.r j))) ω t)
            (uProc (s (d.r j)) u0 (X (s (d.r j))) (Ψ (s (d.r j))) ω t))
        ∂volume ∂M.P) atTop (𝓝 (ENNReal.ofReal (∫ ω, d.runningCost T ω ∂d.Q))) := by
    obtain ⟨K,hK,hB⟩ := hM T T.2
    let e (n : ℕ) (ω : Ω) := ∫⁻ t in Set.Ioc (0:ℝ) (T:ℝ),
      ENNReal.ofReal (Real.exp (-γ*t) * costOfTilde Lt (M.Xhat n (X n) ω t)
        (uProc n u0 (X n) (Ψ n) ω t)) ∂volume
    refine coupled_accumulated_cost_expectations_converge d hs T p hp K hK e ?_ hB
    filter_upwards [eventually_ge_atTop 1] with n hn
    intro ω
    have h := hInt n hn ω
    have hCst (t : ℝ) (ht : 0 ≤ t) :
        0 ≤ Real.exp (-γ*t)*costOfTilde Lt (M.Xhat n (X n) ω t)
          (uProc n u0 (X n) (Ψ n) ω t) :=
      mul_nonneg (Real.exp_nonneg _) (hA2.cost.nonneg _ _ (h.2.2.2.2.2.2.2 t ht))
    constructor
    · simp only [queueHJBObservation,Fin.append_right,Matrix.cons_val_zero]
      exact intervalIntegral.integral_nonneg T.2 (fun t ht => hCst t ht.1)
    · simpa only [queueHJBObservation,Fin.append_right,Matrix.cons_val_zero,e] using
        h.2.2.2.2.2.1 T T.2
  exact ⟨fun t => (hCost t).1,fun T => (hCost T).2⟩
