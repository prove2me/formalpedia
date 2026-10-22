-- Prove2me | solution 1 for JHolomorphic.fderiv_apply_isTestFunction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T13:52:07.81231+00:00
-- url     : https://prove2.me/submissions/b65d981a-a7e3-4598-bde3-95037b76dba0

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp



namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- A directional derivative `z ↦ Dφ(z) v` of a real `C^∞` function `φ` with compact support in
`U` is again a real `C^∞` function with compact support in `U`. -/
theorem fderiv_apply_isTestFunction_aux {U : Set ℂ} {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (v : ℂ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) ∧ HasCompactSupport (fun z => fderiv ℝ φ z v) ∧
      tsupport (fun z => fderiv ℝ φ z v) ⊆ U := by
  have hsub : Function.support (fun z => fderiv ℝ φ z v) ⊆ Function.support (fderiv ℝ φ) :=
    fun x hx h0 => hx (by simp [h0])
  refine ⟨(hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const,
    (hφc.fderiv (𝕜 := ℝ)).mono hsub, ?_⟩
  exact (closure_mono hsub).trans ((tsupport_fderiv_subset ℝ).trans hφU)

end JHolomorphic

open JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

theorem solution {U : Set ℂ} {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (v : ℂ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) ∧ HasCompactSupport (fun z => fderiv ℝ φ z v) ∧
      tsupport (fun z => fderiv ℝ φ z v) ⊆ U :=
  fderiv_apply_isTestFunction_aux hφ hφc hφU v
