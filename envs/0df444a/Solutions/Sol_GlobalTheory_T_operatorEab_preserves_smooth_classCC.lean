-- Prove2me | solution 1 for GlobalTheory.T.operatorEab_preserves_smooth_classCC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:53:14.288054+00:00
-- url     : https://prove2.me/submissions/9445af32-3ca0-49ad-9b98-21748d509792

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OperatorEabPreservesSmoothClassCC
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OperatorEabPreservesSmoothClassCCStatement
import Theorems.Thm_GlobalTheory_EabClass_eh_class


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (A : ℝ) (a b : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (B.CkOn ⊤ (B.GV k r) (Q.EH k r a b f) ∧ ∀ m : ℕ, B.InCC (A) m (Q.EH k r a b f)) := by
  first | exact @GlobalTheory.EabClass.eh_class | exact GlobalTheory.EabClass.eh_class | (intros; apply GlobalTheory.EabClass.eh_class <;> assumption)
end _root_.GlobalTheory.T
