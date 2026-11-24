-- Prove2me | solution 1 for GlobalTheory.T.measurable_coordinate_maps_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:18:07.597523+00:00
-- url     : https://prove2.me/submissions/34a9892c-d431-42c2-b52c-f0c243cbc333

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasurableCoordinateMapsTensor
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasurableCoordinateMapsTensorStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_coordW_one_map_coords


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (M : ℕ) (lam : Measure R), lam.IsAddHaarMeasure → (Measurable fun (X : Fin 1 → Fin M → R ⊗[F] E) (p : Fin M × Fin d) => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2) ∧ (coordW R b lam 1 M).map (fun X (p : Fin M × Fin d) => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2) = Measure.pi fun _ => lam := by
  first | exact @GlobalTheory.CompanionTheory.SW.coordW_one_map_coords | exact GlobalTheory.CompanionTheory.SW.coordW_one_map_coords | (intros; apply GlobalTheory.CompanionTheory.SW.coordW_one_map_coords <;> assumption)
end _root_.GlobalTheory.T
