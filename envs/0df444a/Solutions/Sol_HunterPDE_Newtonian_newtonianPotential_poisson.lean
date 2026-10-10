-- Prove2me | solution 1 for HunterPDE.Newtonian.newtonianPotential_poisson
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T22:40:14.565404+00:00
-- url     : https://prove2.me/submissions/9f6ae988-6f8b-48bd-8556-fa0ed8e765e3

import Theorems.Thm_MeasureTheory_laplacian_convolution_right
import Theorems.Thm_HunterPDE_Newtonian_locallyIntegrable_fundamentalSolution
import Theorems.Thm_HunterPDE_Newtonian_integrable_fundamentalSolution_mul
import Theorems.Thm_HunterPDE_Newtonian_newtonianPotential_laplacian
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory ContinuousLinearMap HunterPDE.Newtonian
open scoped ContDiff Convolution
open Laplacian

theorem solution (n : ℕ) (hn : 2 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    (∀ x, Integrable (fun y => fundamentalSolution n (x - y) * f y)) ∧
      ContDiff ℝ ∞ (newtonianPotential n f) ∧
      ∀ x, -(Δ (newtonianPotential n f)) x = f x := by
  have hK := locallyIntegrable_fundamentalSolution n hn
  have heq (g : EuclideanSpace ℝ (Fin n) → ℝ) :
      newtonianPotential n g = fundamentalSolution n ⋆[lsmul ℝ ℝ] g := by
    rw [← convolution_flip]
    rfl
  refine ⟨fun x => integrable_fundamentalSolution_mul n hn f hf.continuous hfc x, ?_, ?_⟩
  · rw [heq]
    exact hfc.contDiff_convolution_right (lsmul ℝ ℝ) hK hf
  · intro x
    have hcomm := MeasureTheory.laplacian_convolution_right n (fundamentalSolution n) f
      hK (contDiff_infty.mp hf 2) hfc
    rw [← heq f, ← heq (Δ f)] at hcomm
    rw [hcomm]
    simpa using congrArg Neg.neg ((newtonianPotential_laplacian n hn f hf hfc).2 x)
