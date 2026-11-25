-- Prove2me | solution 1 for GlobalTheory.T.continuous_rho_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:44.336611+00:00
-- url     : https://prove2.me/submissions/4afde4f1-c68a-415d-a0fe-be5b8d4ceca8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousRhoApply
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousRhoApplyStatement
import Theorems.Thm_GlobalTheory_RealWeil_continuous_rho


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : Type) [Fintype l] (v : L2 l), Continuous fun w : l ⊕ l → ℝ => rho w v := by
  first | exact @GlobalTheory.RealWeil.continuous_rho | exact GlobalTheory.RealWeil.continuous_rho | (intros; apply GlobalTheory.RealWeil.continuous_rho <;> assumption)
end _root_.GlobalTheory.T
