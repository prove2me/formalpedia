-- Prove2me | solution 1 for GlobalTheory.T.haar_map_linear_scaling_by_determinant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:12:18.099108+00:00
-- url     : https://prove2.me/submissions/9092d883-f03e-47c7-a770-8897fd886930

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMapLinearScalingByDeterminant
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMapLinearScalingByDeterminantStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DetScale_map_mulVec_eq_smul


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
theorem _root_.solution : ∀ (F : Type) [Field F] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ c : ℝ≥0, lam.map (fun x => algebraMap F R A.det * x) = c • lam → ∀ μ : Measure (ι → R), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F R) *ᵥ x) = c • μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul | exact GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul | (intros; apply GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul <;> assumption)
end _root_.GlobalTheory.T
