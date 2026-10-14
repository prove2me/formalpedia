-- Prove2me | solution 1 for HunterPDE.Sobolev.IsTestFunction.iteratedPartial
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:01:42.27991+00:00
-- url     : https://prove2.me/submissions/44b0c104-09f3-4931-b3fe-49db5d3d984f

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Calculus.ContDiff.Comp

open HunterPDE.Sobolev
open scoped ContDiff
set_option autoImplicit false

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : IsTestFunction Ω φ)
    (α : Fin n → ℕ) : IsTestFunction Ω (iteratedPartial α φ) := by
  have hpartial {u : EuclideanSpace ℝ (Fin n) → ℝ}
      (hu : IsTestFunction Ω u) (i : Fin n) : IsTestFunction Ω (partialDeriv i u) := by
    refine ⟨?_, hu.2.1.fderiv_apply ℝ _, (tsupport_fderiv_apply_subset ℝ _).trans hu.2.2⟩
    exact (hu.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp
      (contDiff_id.prodMk contDiff_const)
  have step (i : Fin n) (m : ℕ) {u : EuclideanSpace ℝ (Fin n) → ℝ}
      (hu : IsTestFunction Ω u) : IsTestFunction Ω ((partialDeriv i)^[m] u) := by
    induction m with
    | zero => simpa using hu
    | succ m ih => simpa only [Function.iterate_succ_apply'] using hpartial ih i
  unfold iteratedPartial
  generalize List.finRange n = l
  induction l with
  | nil => exact hφ
  | cons i l ih => exact step i (α i) ih
