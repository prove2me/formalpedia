-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.tubeShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:58:57.941407+00:00
-- url     : https://prove2.me/submissions/9954b4a3-ac73-4dac-9cc6-3c7d98506d65

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomain
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (Ω : Set (ι → ℝ)), IsOpen Ω → IsPreconnected Ω →
    ∀ H : (ι → ℂ) → ℂ, DifferentiableOn ℂ H {z | (fun i => (z i).re) ∈ Ω} →
    (∀ K ⊆ Ω, IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ y : ι → ℝ,
      ‖H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(∑ i, y i ^ 2) / 2)) →
    ∀ x₁ ∈ Ω, ∀ x₂ ∈ Ω,
      (∫ y : ι → ℝ, H (fun i => (x₁ i : ℂ) + (y i : ℂ) * Complex.I)) =
        ∫ y : ι → ℝ, H (fun i => (x₂ i : ℂ) + (y i : ℂ) * Complex.I) := by
  intro ι _ Ω hΩ hc H hH hdec x₁ hx₁ x₂ hx₂
  refine hc.induction₂
    (fun a b => (∫ y : ι → ℝ, H (fun i => (a i : ℂ) + (y i : ℂ) * Complex.I)) =
      ∫ y : ι → ℝ, H (fun i => (b i : ℂ) + (y i : ℂ) * Complex.I)) ?_ ?_ ?_ hx₁ hx₂
  · intro x hx
    obtain ⟨R, hR, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hx)
    obtain ⟨C, hC⟩ := hdec _ hb (isCompact_closedBall x R)
    refine mem_nhdsWithin_of_mem_nhds ?_
    filter_upwards [Metric.closedBall_mem_nhds x (half_pos hR)] with y hy
    exact tubeShift_local Ω H hH x y R C hb hC (Metric.mem_closedBall.1 hy)
  · intro a b c _ _ _ h₁ h₂
    exact h₁.trans h₂
  · intro a b _ _ h
    exact h.symm
end GlobalTheory.CompanionTheory.EisTube
