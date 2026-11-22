-- Prove2me | solution 1 for MasulloGRH.contDiff_integral_of_bounded_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T16:57:57.600193+00:00
-- url     : https://prove2.me/submissions/11ea93ac-7829-4a07-a38b-1528ab4ae355

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false

open MeasureTheory Topology Filter

namespace MasulloGRHParIntAux

variable {Q : Type*} [MeasurableSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem main (F : Q → V → ℂ) (hF : ∀ q, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F q))
    (hmeas : ∀ (k : ℕ) (y : V), AEStronglyMeasurable (fun q => iteratedFDeriv ℝ k (F q) y) μ)
    (hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ q y, ‖iteratedFDeriv ℝ k (F q) y‖ ≤ C) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ q, F q y ∂μ) ∧
      ∀ (k : ℕ) (y : V), iteratedFDeriv ℝ k (fun y => ∫ q, F q y ∂μ) y =
        ∫ q, iteratedFDeriv ℝ k (F q) y ∂μ := by
  set I : (k : ℕ) → V → ContinuousMultilinearMap ℝ (fun _ : Fin k => V) ℂ :=
    fun k y => ∫ q, iteratedFDeriv ℝ k (F q) y ∂μ with hI
  have hdiff : ∀ k q, Differentiable ℝ (iteratedFDeriv ℝ k (F q)) := fun k q =>
    (hF q).differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k)
  have hderiv : ∀ (k : ℕ) (y : V), HasFDerivAt (I k)
      (∫ q, fderiv ℝ (iteratedFDeriv ℝ k (F q)) y ∂μ) y := by
    intro k y
    obtain ⟨C, hC⟩ := hbd (k + 1)
    obtain ⟨C0, hC0⟩ := hbd k
    have hmeas' : ∀ x, AEStronglyMeasurable (fun q => fderiv ℝ (iteratedFDeriv ℝ k (F q)) x) μ :=
      fun x => by
        have := (hmeas (k + 1) x)
        have e : (fun q => fderiv ℝ (iteratedFDeriv ℝ k (F q)) x) =
            fun q => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => V) ℂ)
              (iteratedFDeriv ℝ (k + 1) (F q) x) := by
          funext q
          rw [fderiv_iteratedFDeriv]
          rfl
        rw [e]
        exact (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable this
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C) (s := Set.univ)
      Filter.univ_mem (Eventually.of_forall fun x => hmeas k x)
      (Integrable.of_bound (hmeas k y) C0 (Eventually.of_forall fun q => hC0 q y))
      (hmeas' y) (Eventually.of_forall fun q x _ => ?_) (integrable_const C)
      (Eventually.of_forall fun q x _ => (hdiff k q x).hasFDerivAt)
    rw [norm_fderiv_iteratedFDeriv]
    exact hC q x
  have heq : ∀ k : ℕ, iteratedFDeriv ℝ k (fun y => ∫ q, F q y ∂μ) = I k := by
    intro k
    induction k with
    | zero =>
      funext y
      rw [iteratedFDeriv_zero_eq_comp, hI]
      simp only [Function.comp_apply, iteratedFDeriv_zero_eq_comp]
      exact ((continuousMultilinearCurryFin0 ℝ V ℂ).symm.toLinearIsometry.integral_comp_comm
        (fun q => F q y) (μ := μ)).symm
    | succ k ih =>
      funext y
      rw [iteratedFDeriv_succ_eq_comp_left, ih, Function.comp_apply, (hderiv k y).fderiv, hI]
      exact (LinearIsometry.integral_comp_comm (𝕜 := ℝ)
        (E := V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => V) ℂ)
        (F := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => V) ℂ)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => V) ℂ).symm.toLinearIsometry
        (fun q => fderiv ℝ (iteratedFDeriv ℝ k (F q)) y) (μ := μ)).symm
  refine ⟨contDiff_of_differentiable_iteratedFDeriv fun m _ => ?_, fun k y => by rw [heq k]⟩
  rw [heq m]
  exact fun y => (hderiv m y).differentiableAt

end MasulloGRHParIntAux

open MeasureTheory

theorem solution
    {Q : Type*} [MeasurableSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : Q → V → ℂ) (hF : ∀ q, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F q))
    (hmeas : ∀ (k : ℕ) (y : V), AEStronglyMeasurable (fun q => iteratedFDeriv ℝ k (F q) y) μ)
    (hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ q y, ‖iteratedFDeriv ℝ k (F q) y‖ ≤ C) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ q, F q y ∂μ) ∧
      ∀ (k : ℕ) (y : V), iteratedFDeriv ℝ k (fun y => ∫ q, F q y ∂μ) y =
        ∫ q, iteratedFDeriv ℝ k (F q) y ∂μ :=
  MasulloGRHParIntAux.main μ F hF hmeas hbd
