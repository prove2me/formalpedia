-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_compact_kernel_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:35:55.739386+00:00
-- url     : https://prove2.me/submissions/c1d17b41-97b5-4280-9d94-f76138aa9a14

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch03_reflectionSignedCompactBoundV1
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A continuous kernel along all pairs of times in a compact cadlag path is bounded. -/
theorem solution (X : NNReal → ℝ) (hX : IsCadlag X)
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)))
    (T : NNReal) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc (0 : ℝ) (T : ℝ),
      ∀ r : NNReal, r ≤ T → |g (s,X r)| ≤ M := by
  obtain ⟨a,ha⟩ := Kyprianou.Ch03.reflectionSignedCompactBoundV1 X hX 1 T
  obtain ⟨b,hb⟩ := Kyprianou.Ch03.reflectionSignedCompactBoundV1 X hX (-1) T
  let R := max 0 (max a b)
  have hR (r : NNReal) (hr : r ≤ T) : X r ∈ Icc (-R) R := by
    have h1 : 1 * X r ≤ a := ha ⟨r,⟨zero_le,hr⟩,rfl⟩
    have h2 : -1 * X r ≤ b := hb ⟨r,⟨zero_le,hr⟩,rfl⟩
    have h3 : a ≤ R := (le_max_left _ _).trans (le_max_right _ _)
    have h4 : b ≤ R := (le_max_right _ _).trans (le_max_right _ _)
    exact ⟨by linarith,by linarith⟩
  let K := Icc (0 : ℝ) (T : ℝ) ×ˢ Icc (-R) R
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hsub : K ⊆ Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := fun z hz => ⟨hz.1.1,mem_univ _⟩
  obtain ⟨M,hM⟩ := (hK.image_of_continuousOn (hg.mono hsub).abs).bddAbove
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro s hs r hr
  exact (hM ⟨(s,X r),⟨hs,hR r hr⟩,rfl⟩).trans (le_max_right _ _)
