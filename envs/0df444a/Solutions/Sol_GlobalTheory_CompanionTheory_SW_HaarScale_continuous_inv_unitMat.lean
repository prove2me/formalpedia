-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarScale.continuous_inv_unitMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:45.313877+00:00
-- url     : https://prove2.me/submissions/59a68455-4959-4435-b2f1-8becbea107f4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensor
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousScale

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarScale
variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}
namespace GlobalTheory.CompanionTheory.SW.HaarScale
theorem _root_.solution (hu : IsOpenEmbedding (Units.val : Kˣ → K)) :
    Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} => (g.1)⁻¹ := by
  have hdet : Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} => g.1.det :=
    Continuous.matrix_det continuous_subtype_val
  have hunit : Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} => g.2.unit :=
    hu.isEmbedding.continuous_iff.2 (by simpa [Function.comp_def] using hdet)
  have hinv : Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} =>
      ((g.2.unit⁻¹ : Kˣ) : K) := Units.continuous_val.comp hunit.inv
  have hadj : Continuous fun g : {g : Matrix (Fin n) (Fin n) K // IsUnit g.det} => g.1.adjugate :=
    Continuous.matrix_adjugate continuous_subtype_val
  refine (hinv.smul hadj).congr fun g => ?_
  have hr : Ring.inverse g.1.det = ((g.2.unit⁻¹ : Kˣ) : K) := by
    have h := Ring.inverse_unit g.2.unit
    rwa [IsUnit.unit_spec] at h
  rw [Matrix.inv_def, hr]
  rfl
end GlobalTheory.CompanionTheory.SW.HaarScale
