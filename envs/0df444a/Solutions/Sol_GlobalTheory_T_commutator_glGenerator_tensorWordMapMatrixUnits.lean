-- Prove2me | solution 1 for GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:31:08.530061+00:00
-- url     : https://prove2.me/submissions/6059b972-3706-4bf3-9646-e4cd0a5e842a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutatorGlGeneratorTensorWordMapMatrixUnits
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutatorGlGeneratorTensorWordMapMatrixUnitsStatement
import Theorems.Thm_GlobalTheory_SmoothForms_commutator_wordMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (d : ℕ) (a b : Fin n) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), E a b * wordMap E d M - wordMap E d M * E a b = wordMap E d (polar n d a b * M - M * polar n d a b) := by
  first | exact @GlobalTheory.SmoothForms.commutator_wordMap | exact GlobalTheory.SmoothForms.commutator_wordMap | (intros; apply GlobalTheory.SmoothForms.commutator_wordMap <;> assumption)
end _root_.GlobalTheory.T
