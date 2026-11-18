-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.nearly_optimal_ppr
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:17:23.189719+00:00
-- url     : https://prove2.me/submissions/28522a57-1df8-435a-bb7b-c32ac46c6538
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NearlyOptimalPPR_Computation_local_program_upper_bound
import Theorems.Thm_NearlyOptimalPPR_Computation_explicit_output_lower_bound
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open NearlyOptimalPPR.Computation

lemma step_output_accounting (m : SolveModel) (p : Program) {n : ℕ}
    (g : InputGraph n) (ω : ℕ → Bool) (st : MachineState)
    (h : (st.output.length : ℝ≥0∞) ≤ st.work) :
    ((machineStep m p g ω st).output.length : ℝ≥0∞) ≤
      (machineStep m p g ω st).work := by
  classical
  unfold machineStep
  split
  · exact h
  · split
    · exact h.trans (le_add_right le_rfl)
    · exact h.trans (le_add_right le_rfl)
    · simpa using add_le_add_right h 1
    · dsimp only
      split <;> exact h.trans (le_add_right le_rfl)

theorem output_accounting (m : SolveModel) (p : Program) (n : ℕ)
    (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool) (t : ℕ) :
    ((machineRun m p g s α ε ω t).output.length : ℝ≥0∞) ≤
      (machineRun m p g s α ε ω t).work := by
  induction t with
  | zero => simp [machineRun, machineInit]
  | succ t ih =>
    simpa only [machineRun, Function.iterate_succ_apply'] using
      step_output_accounting m p g ω (machineRun m p g s α ε ω t) ih

theorem solution (m : SolveModel) :
    ∃ (p : Program) (C c : ℝ), admissible p ∧ 0 < C ∧ 0 < c ∧
      (∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ),
        0 < α → α < 1 → 0 < ε → ε ≤ 1 →
          successful m p g s α ε ∧
          Measurable (executionWork m p g s α ε) ∧
          expectedWork m p g s α ε ≤ ENNReal.ofReal (envelope C c ε)) ∧
      subpolynomialEnvelope C c ∧
      explicitOutputLowerBound ∧
      (∀ (p' : Program) (n : ℕ) (g : InputGraph n) (s : Fin n)
        (α ε : ℝ) (ω : ℕ → Bool) (t : ℕ),
        ((machineRun m p' g s α ε ω t).output.length : ℝ≥0∞) ≤
          (machineRun m p' g s α ε ω t).work) := by
  obtain ⟨p, C, c, had, hC, hc, hu, hs⟩ := local_program_upper_bound m
  exact ⟨p, C, c, had, hC, hc, hu, hs, explicit_output_lower_bound,
    fun p' n g s α ε ω t => output_accounting m p' n g s α ε ω t⟩
