-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.logarithmic_control
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:13.70148+00:00
-- url     : https://prove2.me/submissions/8b8dc23f-f996-49df-bfe3-e7d317577022

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_LogarithmicControl
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_uniformTheta_mem
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_exp_sublinear_le
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_outerConstant_ge_one
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_inner_log_bound
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_logarithm_derivative_bound
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_zero_free_disk_logarithm
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_logarithmic_derivative_eq

set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex
open OAI.SevenEighths OAI.SevenEighths.LogarithmicControl
namespace OAI.SevenEighths.LogarithmicControl
theorem _root_.solution {e A M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hA : 1 ≤ A) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a C : ℝ) (L E : ℂ → ℂ) (c : ℂ),
      1 / 2 ≤ a → a ≤ 1 → Real.exp 1 ≤ C →
      DifferentiableOn ℂ L (ball c (2 - a - 2 * e)) →
      (∀ z ∈ ball c (2 - a - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball c (2 - a - 3 * e), ‖L z‖ ≤ C ^ M) →
      DifferentiableOn ℂ E (ball c (1 / 2)) →
      EqOn (Complex.exp ∘ E) L (ball c (1 / 2)) →
      (∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A) →
      (∀ z ∈ closedBall c (2 - a - 6 * e), ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall c (2 - a - 8 * e),
        ‖deriv L z / L z‖ ≤ (outerConstant e A M / (2 * e)) * Real.log C) := by
  have hθ := uniformTheta_mem he he'
  have hB := outerConstant_ge_one he he' hA hM
  have hK : 0 ≤ A * outerConstant e A M := by positivity
  obtain ⟨D, hD, hDb⟩ := exp_sublinear_le hθ.1.le hθ.2 hK hε
  refine ⟨2 * D, by positivity, ?_⟩
  intro a C L E c ha ha' hC hL h0 hpoly hE hEL hEb
  have hCp : 0 < C := (Real.exp_pos 1).trans_le hC
  have hT : 1 ≤ Real.log C := by simpa using Real.log_le_log (Real.exp_pos 1) hC
  obtain ⟨g, hg, hge, hgin, hgRe⟩ :=
    zero_free_disk_logarithm ha' he he' hCp hL h0 hpoly hE hEL hEb
  constructor
  · intro z hz
    have hz' : z ∈ ball c (2 - a - 2 * e) :=
      closedBall_subset_ball (by linarith) hz
    have hez : Complex.exp (g z) = L z := hge hz'
    have hb := inner_log_bound ha ha' he he' hA hM hT hg hgRe hgin hz
    have hp : Real.exp (A * outerConstant e A M * Real.log C ^ uniformTheta e) ≤
        D * C ^ ε := by
      convert hDb (Real.log C) hT using 1
      rw [Real.rpow_def_of_pos hCp, mul_comm ε]
    have hu : ‖L z‖ ≤ D * C ^ ε := by
      rw [← hez, Complex.norm_exp]
      exact (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hb)).trans hp
    have hl : ‖(L z)⁻¹‖ ≤ D * C ^ ε := by
      rw [← hez, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
      have hre : -(g z).re ≤ ‖g z‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      exact (Real.exp_le_exp.mpr (hre.trans hb)).trans hp
    nlinarith
  · intro z hz
    rw [logarithmic_derivative_eq isOpen_ball hg hge
      (closedBall_subset_ball (by linarith) hz)]
    exact logarithm_derivative_bound ha ha' he he' hA hM hT hg hgRe
      (hgin c (mem_closedBall_self (by norm_num))) hz
end OAI.SevenEighths.LogarithmicControl
