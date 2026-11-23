-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TupFubini.piFinSuccAbove_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:13.972965+00:00
-- url     : https://prove2.me/submissions/3b39f62d-a05b-46ab-be0b-ff81e6354aa5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionPreservesHaarLocalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureOrthogonalExtension

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
theorem _root_.solution {A : Type} [MeasurableSpace A] {n : ℕ} (x : A) (Y : Fin n → A) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) 0).symm (x, Y) = Fin.cons x Y := by
  apply (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) 0).injective
  rw [MeasurableEquiv.apply_symm_apply]
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
end GlobalTheory.CompanionTheory.SW.TupFubini
