-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.nrm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:29.252463+00:00
-- url     : https://prove2.me/submissions/4812700f-d0a0-46c2-8b16-8bc65070f2ae

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_repr_mul

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimGood
variable {L K : Type} [Field L] [CommRing K] [Algebra L K] (B : Module.Basis (Fin 2) L K)
variable {B} {Δ : L}
namespace GlobalTheory.CompanionTheory.SW.PrimGood
theorem _root_.solution (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ) (x y : K) :
    nrm B Δ (x * y) = nrm B Δ x * nrm B Δ y := by
  obtain ⟨e0, e1⟩ := repr_mul h0 h1 x y
  unfold nrm
  rw [e0, e1]; ring
end GlobalTheory.CompanionTheory.SW.PrimGood
