-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuotVan.map_withDensity_eq_of_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:57:43.355381+00:00
-- url     : https://prove2.me/submissions/48eab799-e2d0-48fa-a1a9-850f431f72bb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TopoPolish
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapWithDensityEqOfScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuotVan
namespace GlobalTheory.CompanionTheory.QuotVan
theorem _root_.solution {X : Type*} [MeasurableSpace X] (ρ : Measure X) (S : X → X)
    (hS : Measurable S) (f : X → ℝ≥0∞) (hf : Measurable f) (a : ℝ≥0∞) (ha0 : a ≠ 0) (hat : a ≠ ∞)
    (hρ : ρ.map S = a • ρ) (hfS : ∀ x, f (S x) = a * f x) :
    (ρ.withDensity f).map S = ρ.withDensity f := by
  ext A hA
  rw [map_apply hS hA, withDensity_apply _ (hS hA), withDensity_apply _ hA]
  have key : ∫⁻ x, (A.indicator f) x ∂(ρ.map S) = a * ∫⁻ x, A.indicator f x ∂ρ := by
    rw [hρ, lintegral_smul_measure]; rfl
  rw [lintegral_map (hf.indicator hA) hS] at key
  have h2 : (fun x => A.indicator f (S x)) = fun x => a * (S ⁻¹' A).indicator f x := by
    funext x
    by_cases hx : S x ∈ A
    · have hx' : x ∈ S ⁻¹' A := hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', hfS]
    · have hx' : x ∉ S ⁻¹' A := hx
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]
  rw [h2, lintegral_const_mul _ (hf.indicator (hS hA)), lintegral_indicator (hS hA),
    lintegral_indicator hA] at key
  exact (ENNReal.mul_right_inj ha0 hat).1 key
end GlobalTheory.CompanionTheory.QuotVan
