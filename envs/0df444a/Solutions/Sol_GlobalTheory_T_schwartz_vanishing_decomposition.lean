-- Prove2me | solution 1 for GlobalTheory.T.schwartz_vanishing_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:58.86963+00:00
-- url     : https://prove2.me/submissions/624d6d99-3133-4d4c-9395-dc92c343a079

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecompositionStatement
import Theorems.Thm_GlobalTheory_SchwartzDiv_hadamard


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ), f 0 = 0 → ∃ (n : ℕ) (L : Fin n → V →L[ℝ] ℝ) (h g : Fin n → SchwartzMap V ℂ),
      (∀ i x, g i x = (L i x : ℂ) * h i x) ∧ ∀ x, f x = ∑ i, g i x := by
  first | exact @GlobalTheory.SchwartzDiv.hadamard | exact GlobalTheory.SchwartzDiv.hadamard | (intros; apply GlobalTheory.SchwartzDiv.hadamard <;> assumption)
end _root_.GlobalTheory.T
