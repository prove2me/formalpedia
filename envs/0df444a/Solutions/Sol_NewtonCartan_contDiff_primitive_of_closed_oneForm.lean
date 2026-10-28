-- Prove2me | solution 1 for NewtonCartan.contDiff_primitive_of_closed_oneForm
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:51:05.082985+00:00
-- url     : https://prove2.me/submissions/53abbe88-3782-4a58-94fa-45fe1307bc55

import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped ContDiff Topology
open MeasureTheory Set Convex

theorem solution
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [FiniteDimensional ℝ X]
    (omegaForm : X → X →L[ℝ] ℝ) (hω : ContDiff ℝ ∞ omegaForm)
    (hclosed : ∀ a x y, fderiv ℝ omegaForm a x y = fderiv ℝ omegaForm a y x) :
    ∃ φ : X → ℝ, ContDiff ℝ ∞ φ ∧ ∀ a, HasFDerivAt φ (omegaForm a) a := by
  have hdiffOn : DifferentiableOn ℝ omegaForm univ :=
    (hω.differentiable (by simp)).differentiableOn
  obtain ⟨φ, hφ⟩ :=
    (convex_univ : Convex ℝ (univ : Set X)).exists_forall_hasFDerivAt_of_fderiv_symmetric
      isOpen_univ hdiffOn (fun a _ha x y => hclosed a x y)
  have hHas : ∀ a, HasFDerivAt φ (omegaForm a) a := fun a => hφ a (mem_univ a)
  have hDifferentiable : Differentiable ℝ φ := fun a => (hHas a).differentiableAt
  have hfd : fderiv ℝ φ = omegaForm := by
    funext a
    exact (hHas a).fderiv
  refine ⟨φ, ?_, hHas⟩
  exact contDiff_infty_iff_fderiv.2 ⟨hDifferentiable, hfd ▸ hω⟩
