-- Prove2me | solution 1 for MeasureTheory.integral_polar_sphere_centered
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T10:24:05.920975+00:00
-- url     : https://prove2.me/submissions/de278ccd-c829-4bac-9539-2d4555b82d8b

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory MeasureTheory.Measure Set Metric Filter Function
open scoped Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section
namespace DirectionalBallWork

/-- Polar integration centered at an arbitrary point, before removing radial density. -/
theorem integral_polar {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Integrable f) :
    (∫ y, f y) =
      ∫ t : Ioi (0 : ℝ),
        ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          f (x + t.1 • ω.1) ∂volume.toSphere ∂Measure.volumeIoiPow (n - 1) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let E := EuclideanSpace ℝ (Fin n)
  let S := sphere (0 : E) 1
  let T := Ioi (0 : ℝ)
  let μ : Measure E := volume
  let σ : Measure S := μ.toSphere
  let ν : Measure T := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  let w : E → ℝ := fun y => f (x + y)
  have hw : Integrable w μ :=
    ((measurePreserving_add_left μ x).integrable_comp hf.aestronglyMeasurable).2 hf
  have hw' : Integrable (fun y : ({0}ᶜ : Set E) => w y.1) (μ.comap (↑)) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).1 hw.integrableOn
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
  have hprod : Integrable (fun p : S × T => w (p.2.1 • p.1.1)) (σ.prod ν) := by
    have hh := hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)
      (g := fun p => w ((homeomorphUnitSphereProd E).symm p).1)
    simp only [Function.comp_def, Homeomorph.symm_apply_apply] at hh
    simpa only [homeomorphUnitSphereProd_symm_apply_coe] using hh.mp hw'
  have hp : (∫ y, f y ∂μ) =
      ∫ t : T, ∫ z : S, f (x + t.1 • z.1) ∂σ ∂ν := by
    calc
      (∫ y, f y ∂μ) = ∫ y, w y ∂μ := (integral_add_left_eq_self f x).symm
      _ = ∫ y : ({0}ᶜ : Set E), w y.1 ∂(μ.comap (↑)) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl,
          restrict_compl_singleton]
      _ = ∫ p : S × T, w (p.2.1 • p.1.1) ∂(σ.prod ν) := by
        simpa only [Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe] using
          hmp.integral_comp (Homeomorph.measurableEmbedding _)
            (fun p => w ((homeomorphUnitSphereProd E).symm p).1)
      _ = _ := integral_prod_symm _ hprod
  simpa [μ, σ, ν, E] using hp


end DirectionalBallWork

theorem solution {n : ℕ} (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Integrable f) :
    (∫ y, f y) = ∫ t : Ioi (0 : ℝ),
      ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        f (x + t.1 • ω.1) ∂volume.toSphere ∂Measure.volumeIoiPow (n - 1) := by
  exact DirectionalBallWork.integral_polar hn x f hf
