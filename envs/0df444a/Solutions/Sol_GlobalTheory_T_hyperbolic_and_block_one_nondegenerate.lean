-- Prove2me | solution 1 for GlobalTheory.T.hyperbolic_and_block_one_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:52.08731+00:00
-- url     : https://prove2.me/submissions/ad0a7f47-0524-4a0b-a272-195b76aa914f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HyperbolicAndBlockOneNondegenerate
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HyperbolicAndBlockOneNondegenerateStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_blockForms_isHermND


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypJ J) ∧ ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND | exact GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND | (intros; apply GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND <;> assumption)
end _root_.GlobalTheory.T
