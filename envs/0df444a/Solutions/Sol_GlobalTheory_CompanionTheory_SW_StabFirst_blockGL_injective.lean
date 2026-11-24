-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.blockGL_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:36:10.3528+00:00
-- url     : https://prove2.me/submissions/0e3bf13b-4f89-45b4-964b-3fba437fa59e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_blockOne_right_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_coe_blockGL

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
theorem _root_.solution : Function.Injective (blockGL : GL (Fin M) K → GL (Fin (M + 1)) K) := by
  intro a b h
  apply Units.ext
  apply blockOne_right_injective (a := (1 : K)) (b := 1)
  simpa [coe_blockGL] using congrArg (fun g : GL (Fin (M + 1)) K =>
    (g : Matrix (Fin (M + 1)) (Fin (M + 1)) K)) h
end GlobalTheory.CompanionTheory.SW.StabFirst
