-- Prove2me | solution 1 for Newton.tail_bound_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:00:42.091903+00:00
-- url     : https://prove2.me/submissions/0baaa4f8-ff67-418f-8908-6467375856b9

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense

set_option autoImplicit false
open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (F : (Fin n → ℝ) → ℝ) {R₁ R₂ ε : ℝ} (hR : R₁ ≤ R₂) (h_nonneg : ∀ x, 0 ≤ F x)
    (h_int : Integrable F (volume.restrict {x | R₁ ≤ ‖x‖}))
    (h_bound : ∫ x, F x ∂(volume.restrict {x | R₁ ≤ ‖x‖}) < ε) :
    ∫ x, F x ∂(volume.restrict {x | R₂ ≤ ‖x‖}) < ε := by
  set S₁ : Set (Fin n → ℝ) := {x | R₁ ≤ ‖x‖}
  set S₂ : Set (Fin n → ℝ) := {x | R₂ ≤ ‖x‖}
  have h_subset : S₂ ⊆ S₁ := by
    intro x hx
    have hR₂ : R₂ ≤ ‖x‖ := hx
    exact le_trans hR hR₂
  have hμ_le : (volume.restrict S₂) ≤ (volume.restrict S₁) :=
    Measure.restrict_mono_set (μ := volume) h_subset
  have h_nonneg_ae : 0 ≤ᵐ[volume.restrict S₁] fun x => F x :=
    Filter.Eventually.of_forall h_nonneg
  have h_le :=
    integral_mono_measure (μ := volume.restrict S₂) (ν := volume.restrict S₁)
      hμ_le h_nonneg_ae h_int
  have h_le_real :
      ∫ x, F x ∂(volume.restrict S₂) ≤ ∫ x, F x ∂(volume.restrict S₁) := h_le
  exact lt_of_le_of_lt h_le_real h_bound
end Newton
