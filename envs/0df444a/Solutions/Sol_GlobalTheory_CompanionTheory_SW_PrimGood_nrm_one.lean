-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.nrm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:30.077435+00:00
-- url     : https://prove2.me/submissions/79b42002-bbc6-4c65-bfdc-a07f1fa001d5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_repr_one

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
theorem _root_.solution (h0 : B 0 = 1) : nrm B Δ (1 : K) = 1 := by
  obtain ⟨e0, e1⟩ := repr_one h0
  unfold nrm
  rw [e0, e1]; ring
end GlobalTheory.CompanionTheory.SW.PrimGood
