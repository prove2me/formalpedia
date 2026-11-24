-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodIso.mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:05:09.524332+00:00
-- url     : https://prove2.me/submissions/6581e30a-fe39-42d8-9588-f3944a3607f7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlacesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnitStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormsIntegrallyEquivalentAlmostAll

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodIso
namespace GlobalTheory.CompanionTheory.SW.GoodIso
theorem _root_.solution {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (P : Matrix (Fin m) (Fin m) R)
    (hP : ∀ i j, P i j ∈ O) (x : Fin m → R) (hx : ∀ i, x i ∈ O) (i : Fin m) : P.mulVec x i ∈ O := by
  change ∑ j, P i j * x j ∈ O
  exact O.sum_mem fun j _ => O.mul_mem (hP i j) (hx j)
end GlobalTheory.CompanionTheory.SW.GoodIso
