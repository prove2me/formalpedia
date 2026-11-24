-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TupFubini.lintegral_tuple_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:35:10.768642+00:00
-- url     : https://prove2.me/submissions/6de6459c-f27c-47a8-8aea-9ada9bde8fda

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionPreservesHaarLocalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureOrthogonalExtension
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TupFubini_piFinSuccAbove_symm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TupFubini
variable {T : Type} [MeasurableSpace T]
namespace GlobalTheory.CompanionTheory.SW.TupFubini
theorem _root_.solution (m : Measure T) [SigmaFinite m] (n N : ℕ)
    (ψ : (Fin (n + 1) → Fin N → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ X, ψ X ∂(Measure.pi fun _ : Fin (n + 1) => Measure.pi fun _ : Fin N => m) =
      ∫⁻ y : Fin 1 → Fin N → T, ∫⁻ Y : Fin n → Fin N → T, ψ (Fin.cons (y 0) Y)
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin N => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin N => m) := by
  set P : Measure (Fin N → T) := Measure.pi fun _ : Fin N => m with hP
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0
  have h2 := measurePreserving_funUnique P (Fin 1)
  have hg : Measurable fun p : (Fin N → T) × (Fin n → Fin N → T) =>
      ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin N → T) 0).symm p) :=
    hψ.comp (MeasurableEquiv.measurable _)
  rw [← h1.symm.lintegral_comp hψ, lintegral_prod _ hg.aemeasurable,
    ← h2.lintegral_comp hg.lintegral_prod_right']
  refine lintegral_congr fun y => lintegral_congr fun Y => ?_
  rw [piFinSuccAbove_symm_apply]
  rfl
end GlobalTheory.CompanionTheory.SW.TupFubini
