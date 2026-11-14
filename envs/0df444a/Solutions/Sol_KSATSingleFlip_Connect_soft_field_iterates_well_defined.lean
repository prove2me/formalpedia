-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_iterates_well_defined
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:00:29.781197+00:00
-- url     : https://prove2.me/submissions/239f3395-9b89-463e-8a55-7f763810770c

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_update_closed
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem solution (γ : ℝ) : ∀ r : ℕ,
    IsFiniteMeasure (nuIter γ r) ∧
    Measure.map (fun z : ℝ => -z) (nuIter γ r) = nuIter γ r ∧
    (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂(nuIter γ r)) ≠ ∞ ∧
    (massM (nuIter γ (r+1))).toReal = Real.exp (-γ)*Real.exp (hPot (nuIter γ r)) ∧
    (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂(nuIter γ (r+1))) =
      ENNReal.ofReal (Real.exp (-γ)*Real.exp ((∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂(nuIter γ r)).toReal)) := by
  have hclosure : ∀ r : ℕ, IsFiniteMeasure (nuIter γ r) ∧
      Measure.map (fun z : ℝ => -z) (nuIter γ r) = nuIter γ r ∧
      (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂(nuIter γ r)) ≠ ∞ := by
    intro r
    induction r with
    | zero =>
      refine ⟨?_,?_,?_⟩
      · change IsFiniteMeasure (0 : Measure ℝ)
        infer_instance
      · simp [nuIter]
      · simp [nuIter]
    | succ r ih =>
      obtain ⟨_,hsym,hu⟩ := ih
      have hh := soft_field_update_closed (nuIter γ r) (Real.exp (-γ)) (le_of_lt (Real.exp_pos _)) hsym hu
      change IsFiniteMeasure (Rbeta (Real.exp (-γ)) (nuIter γ r)) ∧ _
      refine ⟨hh.1,hh.2.1,?_⟩
      change (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂(Rbeta (Real.exp (-γ)) (nuIter γ r))) ≠ ∞
      rw [hh.2.2.2]
      exact ENNReal.ofReal_ne_top
  intro r
  obtain ⟨hf,hsym,hu⟩ := hclosure r
  have hh := soft_field_update_closed (nuIter γ r) (Real.exp (-γ)) (le_of_lt (Real.exp_pos _)) hsym hu
  refine ⟨hf,hsym,hu,?_,?_⟩
  · exact hh.2.2.1
  · exact hh.2.2.2
