-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarCoord.haar_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:41.465163+00:00
-- url     : https://prove2.me/submissions/d699f10b-2dd5-43bd-b197-b265db63cc4f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarCoord
namespace GlobalTheory.CompanionTheory.SW.HaarCoord
theorem _root_.solution {G H : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [MeasurableSpace H] [BorelSpace H] (f : G → H) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hf : IsHomeomorph f) (μ : Measure H) [μ.IsAddHaarMeasure] :
    (Measure.comap f μ).IsAddHaarMeasure := by
  let h : G ≃ₜ H := hf.homeomorph f
  let e : H ≃+ G := (AddEquiv.mk' h.toEquiv hadd).symm
  have hc : Measure.comap f μ = Measure.map e μ :=
    (MeasurableEquiv.map_symm (μ := μ) h.toMeasurableEquiv).symm
  rw [hc]
  exact e.isAddHaarMeasure_map μ h.symm.continuous h.continuous
end GlobalTheory.CompanionTheory.SW.HaarCoord
