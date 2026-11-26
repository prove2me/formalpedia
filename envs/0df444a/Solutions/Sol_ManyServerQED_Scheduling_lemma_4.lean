-- Prove2me | solution 1 for ManyServerQED.Scheduling.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:21:48.430403+00:00
-- url     : https://prove2.me/submissions/f597fed9-64ee-4ef6-ac25-b2dd9f148869

import Theorems.Thm_ManyServerQED_Scheduling_fluid_occupancies_uoc
import Theorems.Thm_ManyServerQED_Scheduling_queue_primitives_functional_clt

open MeasureTheory ProbabilityTheory Filter Topology
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (mL mU : ℝ)
    (hA3 : M.Assumption3 mL mU) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hpol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n)) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (B : Fin (k + k + k) → ℝ≥0 → Ω' → ℝ),
      IsProbabilityMeasure P' ∧ (∀ j, IsBrownianReal (B j) P') ∧
      iIndepFun (fun j ω (t : ℝ≥0) => B j t ω) P' ∧
      CouplingConverges M.P P'
        (fun n ω t => Fin.append (Fin.append (M.Ahat n ω t) (M.Shat n ω t)) (M.Rhat n ω t))
        (fun ω t j => Fin.append (Fin.append (fun i => Real.sqrt (M.lam i * M.cU2 i))
            (fun i => Real.sqrt (M.mu i))) (fun i => Real.sqrt (M.theta i)) j *
          B j t.toNNReal ω)) ∧
    UocInProb M.P (fun n ω t => Psibar n (Ψ n) ω t) (fun _ => M.rho) ∧
    UocInProb M.P (fun n ω t => Phibar n (X n) (Ψ n) ω t) (fun _ => 0) := by
  exact ⟨queue_primitives_functional_clt M,
    fluid_occupancies_uoc M X0 x hX0 X Ψ
      (fun n hn => (hpol n hn).1.controlled) (fun n hn => (hpol n hn).2.2)⟩
