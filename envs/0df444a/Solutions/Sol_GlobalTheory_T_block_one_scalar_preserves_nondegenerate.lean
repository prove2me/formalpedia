-- Prove2me | solution 1 for GlobalTheory.T.block_one_scalar_preserves_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:51:20.085831+00:00
-- url     : https://prove2.me/submissions/e389661a-c697-4664-b413-c146548a3887

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerate
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__isHermND_blockOne_algebraMap_4c79e73c2c38


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap <;> assumption)
end _root_.GlobalTheory.T
