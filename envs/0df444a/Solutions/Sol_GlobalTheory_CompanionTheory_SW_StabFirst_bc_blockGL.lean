-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.bc_blockGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:33:39.017334+00:00
-- url     : https://prove2.me/submissions/bbc369e6-a01f-440f-8ea2-39c1c804ea04

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {K : Type} [CommRing K] {M : ℕ}
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution {L : Type} [CommRing L] (φ : K →+* L) (g : GL (Fin M) K) :
    bc φ (blockGL g) = blockGL (bc φ g) := by
  apply Units.ext
  change (blockOne 1 (g : Matrix (Fin M) (Fin M) K)).map φ =
    blockOne 1 ((g : Matrix (Fin M) (Fin M) K).map φ)
  rw [map_blockOne, map_one]
end GlobalTheory.CompanionTheory.SW.StabFirst
