-- Prove2me | solution 1 for LLMThroughput.TokenBudget.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:43:58.152202+00:00
-- url     : https://prove2.me/submissions/4e87de32-5905-4c6c-9d77-0fc9892629e7

import Theorems.Thm_LLMThroughput_TokenBudget_theorem_2_a
import Theorems.Thm_LLMThroughput_TokenBudget_theorem_2_b

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LLMThroughput.TokenBudget

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Params) (hP : P.Valid) (vpmax vdmax : ℕ) (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ)
    (hA : IIDArrivals μ a v vpmax vdmax) :
    -- (a) instability under every scheduling algorithm
    ((P.bmax : ℝ) / (P.t P.bmax : ℝ) < arrivalRate μ a * (meanPrefill μ v + meanDecode μ v) →
      ∀ π : Policy, IsScheduler P π → ∀ x : State, Admissible P.bmax x →
        ∀ᵐ ω ∂μ, Tendsto
          (fun n => totalTokens (run P π x (fun m => a m ω) (fun i => v i ω) n)) atTop atTop) ∧
    -- (b) stability under every work-conserving K-FCFS algorithm
    (arrivalRate μ a * (meanPrefill μ v + meanDecode μ v) < (P.bmax : ℝ) / (P.t P.bmax : ℝ) →
      ∀ (K : ℕ) (π : Policy), IsScheduler P π → IsWorkConserving P π → IsKFCFS P K π →
        ∃ F : Finset (ℕ × List (ℕ × ℕ)), ∀ x : State, Admissible P.bmax x →
          (∀ r ∈ x.reqs, r.P ≤ vpmax ∧ r.D ≤ vdmax) →
          ∫⁻ ω, ((hitTime F (run P π x (fun m => a m ω) (fun i => v i ω)) : ℕ∞) : ℝ≥0∞) ∂μ
            < ⊤) :=
  ⟨fun h => theorem_2_a μ P hP vpmax vdmax a v hA h,
   fun h => theorem_2_b μ P hP vpmax vdmax a v hA h⟩
