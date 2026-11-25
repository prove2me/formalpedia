-- Prove2me | solution 1 for GlobalTheory.T.finite_image_compact_right_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:17:07.668593+00:00
-- url     : https://prove2.me/submissions/8c2ed182-841b-4627-9200-641e88c44a2d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteImageCompactRightInvariant
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteImageCompactRightInvariantStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TopGroup_finite_image_of_right_invariant_near_one


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
theorem _root_.solution : ∀ {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Set Γ), IsCompact K → ∀ Gf : Γ → X, {s : Γ | ∀ x, Gf (x * s) = Gf x} ∈ nhds (1 : Γ) → (Gf '' K).Finite := by
  first | exact @GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one | exact GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one | (intros; apply GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one <;> assumption)
end _root_.GlobalTheory.T
