-- Prove2me | solution 1 for GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:18:41.168716+00:00
-- url     : https://prove2.me/submissions/147a64a9-0307-4200-a8a2-8c378c8885d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactGLBoundedEntriesCompletionFinitePlace
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactGLBoundedEntriesCompletionFinitePlaceStatement
import Theorems.Thm_GlobalTheory_BoundedGL_isCompact_bounded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (c : WithZero (Multiplicative ℤ)), IsCompact {g : GL (Fin n) (w.adicCompletion E) | ∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧ Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
  first | exact @GlobalTheory.BoundedGL.isCompact_bounded | exact GlobalTheory.BoundedGL.isCompact_bounded | (intros; apply GlobalTheory.BoundedGL.isCompact_bounded <;> assumption)
end _root_.GlobalTheory.T
