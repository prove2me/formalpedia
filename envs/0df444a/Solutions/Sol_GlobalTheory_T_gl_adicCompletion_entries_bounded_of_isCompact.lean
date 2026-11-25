-- Prove2me | solution 1 for GlobalTheory.T.gl_adicCompletion_entries_bounded_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:19:33.110494+00:00
-- url     : https://prove2.me/submissions/d8017203-063f-4dd7-977c-6a334172d0a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlAdicCompletionEntriesBoundedOfIsCompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlAdicCompletionEntriesBoundedOfIsCompactStatement
import Theorems.Thm_GlobalTheory_BCT_SuppFin_gl_entries_bounded_of_isCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (D : Set (GL (Fin n) (w.adicCompletion E))), IsCompact D → ∃ N : ℤ, ∀ h ∈ D, ∀ i j, Valued.v (h.val i j) ≤ WithZero.exp N ∧ Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := by
  first | exact @GlobalTheory.BCT.SuppFin.gl_entries_bounded_of_isCompact | exact GlobalTheory.BCT.SuppFin.gl_entries_bounded_of_isCompact | (intros; apply GlobalTheory.BCT.SuppFin.gl_entries_bounded_of_isCompact <;> assumption)
end _root_.GlobalTheory.T
