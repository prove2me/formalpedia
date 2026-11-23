-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.DetScale.char_smul_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:49.233555+00:00
-- url     : https://prove2.me/submissions/b9a4e339-1c7d-41be-aba1-a01913f04016

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMapLinearScalingByDeterminant

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DetScale
open Matrix
open scoped Pointwise
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R]
  [BorelSpace R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.DetScale
theorem _root_.solution (lam : Measure R) [lam.IsAddHaarMeasure] (u : Rˣ) :
    distribHaarChar R u • lam.map (fun x => (u : R) * x) = lam := by
  have hm : Measurable fun x : R => (u : R) * x :=
    (continuous_const.mul continuous_id).measurable
  ext S hS
  rw [Measure.smul_apply, Measure.map_apply hm hS]
  have h1 := distribHaarChar_mul lam u ((fun x : R => (u : R) * x) ⁻¹' S)
  have e : u • ((fun x : R => (u : R) * x) ⁻¹' S) = S := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e] at h1
  rw [ENNReal.smul_def, smul_eq_mul]
  exact h1
end GlobalTheory.CompanionTheory.SW.DetScale
