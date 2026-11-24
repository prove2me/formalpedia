-- Prove2me | solution 1 for GlobalTheory.T.permutationWord_gelfandPolynomial_mod_shorter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:46:07.78161+00:00
-- url     : https://prove2.me/submissions/bb94f932-84b6-43c7-a1d5-1494793de135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorterStatement
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_permWord


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
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (d : ℕ) (π : Equiv.Perm (Fin d)), ∃ c ∈ Algebra.adjoin ℂ (Set.range (gelfA E)), wordMap E d (permMat n d π) - c ∈ filt E d := by
  first | exact @GlobalTheory.SmoothForms.PermWord.permWord | exact GlobalTheory.SmoothForms.PermWord.permWord | (intros; apply GlobalTheory.SmoothForms.PermWord.permWord <;> assumption)
end _root_.GlobalTheory.T
