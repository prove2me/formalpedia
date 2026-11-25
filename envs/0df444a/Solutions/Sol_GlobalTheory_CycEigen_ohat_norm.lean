-- Prove2me | solution 1 for GlobalTheory.CycEigen.ohat_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:29:40.68943+00:00
-- url     : https://prove2.me/submissions/49bb66d7-75a2-40cc-953c-4827f53bc878

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycEigen
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycEigen
theorem _root_.solution (K : FinExt l) {y : PadicComplex l} (hy : y ∈ Ohat K) : ‖y‖ ≤ 1 := by
  have : closure (intC (Kinf K)) ⊆ {y : PadicComplex l | ‖y‖ ≤ 1} :=
    closure_minimal (fun _ h => h.2) (isClosed_le continuous_norm continuous_const)
  exact this hy
end GlobalTheory.CycEigen
