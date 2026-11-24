-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodRing.coord_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:55.001297+00:00
-- url     : https://prove2.me/submissions/76e94016-e2a5-4940-b840-425504ee678d

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
theorem _root_.solution {ι₁ ι₂ : Type} [Fintype ι₁] (P : Module.Basis ι₁ K A) (Q : Module.Basis ι₂ K A)
    (hPQ : ∀ i l, Q.repr (P i) l ∈ R) (y : A) (hy : ∀ i, P.repr y i ∈ R) (l : ι₂) :
    Q.repr y l ∈ R := by
  rw [← P.sum_repr y, map_sum, Finsupp.finset_sum_apply]
  refine R.sum_mem fun i _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact R.mul_mem (hy i) (hPQ i l)
end GlobalTheory.CompanionTheory.SW.GoodRing
