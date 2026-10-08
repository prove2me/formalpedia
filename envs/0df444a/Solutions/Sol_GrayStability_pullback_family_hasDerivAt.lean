-- Prove2me | solution 1 for GrayStability.pullback_family_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T14:53:20.728336+00:00
-- url     : https://prove2.me/submissions/e0d6255a-0f98-43a6-a797-1148c17b9b35

import Definitions.Def_GrayStability_Basic
import Theorems.Thm_ParameterizedCalculus_family_comp_hasDerivAt
import Theorems.Thm_FlowCalculus_spatial_differential_hasDerivAt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped ContDiff
open GrayStability

theorem solution {n : ℕ} (η : ℝ → OneForm n) (hη : IsSmoothFamily η)
    (X : ℝ → E n → E n) (hX : ContDiff ℝ ∞ (fun p : ℝ × E n => X p.1 p.2))
    (ψ : ℝ → E n → E n) (hψ : ContDiff ℝ ∞ (fun p : ℝ × E n => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hbij : ∀ t, Function.Bijective (ψ t))
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t)
    (t : ℝ) (y v : E n) :
    HasDerivAt (fun s => pullback (ψ s) (η s) y v)
      (formTimeDeriv η t (ψ t y) (fderiv ℝ (ψ t) y v) +
        lieDerivOneForm (X t) (η t) (ψ t y) (fderiv ℝ (ψ t) y v)) t := by
  have hc := ParameterizedCalculus.family_comp_hasDerivAt η hη
    (fun s => ψ s y) t (X t (ψ t y)) (hflow t y)
  have hv := FlowCalculus.spatial_differential_hasDerivAt X hX ψ hψ hflow t y v
  have ht : DifferentiableAt ℝ (fun s => η s (ψ t y)) t := by
    exact ((hη.comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp)).differentiableAt
  have heval : deriv (fun s => η s (ψ t y)) t (fderiv ℝ (ψ t) y v) =
      formTimeDeriv η t (ψ t y) (fderiv ℝ (ψ t) y v) := by
    simpa [formTimeDeriv] using (ht.hasDerivAt.clm_apply
      (hasDerivAt_const t (fderiv ℝ (ψ t) y v))).deriv.symm
  simpa [pullback, lieDerivOneForm, ContinuousLinearMap.add_apply, heval, add_assoc]
    using hc.clm_apply hv
