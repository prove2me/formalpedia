-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodRing.eq_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:09:32.0878+00:00
-- url     : https://prove2.me/submissions/0d25854d-f397-4369-b5ca-fa1fa0a1eba1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodRing
variable {K A : Type} [Field K] [CommRing A] [Algebra K A] (R : Subring K)
namespace GlobalTheory.CompanionTheory.SW.GoodRing
theorem _root_.solution (B : Module.Basis (Fin 2) K A) (hB0 : B 0 = 1) (y : A) :
    y = algebraMap K A (B.repr y 0) + algebraMap K A (B.repr y 1) * B 1 := by
  conv_lhs => rw [← B.sum_repr y]
  rw [Fin.sum_univ_two, hB0, Algebra.smul_def, Algebra.smul_def, mul_one]
end GlobalTheory.CompanionTheory.SW.GoodRing
