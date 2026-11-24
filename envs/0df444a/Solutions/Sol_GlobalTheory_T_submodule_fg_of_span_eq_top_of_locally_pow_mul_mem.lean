-- Prove2me | solution 1 for GlobalTheory.T.submodule_fg_of_span_eq_top_of_locally_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:19.247968+00:00
-- url     : https://prove2.me/submissions/21fb94a7-4923-4483-a769-ebe644a2b610

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubmoduleFgOfLocallyLeFg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubmoduleFgOfLocallyLeFgStatement
import Theorems.Thm_GlobalTheory_submodule_fg_of_locally_le_fg


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
theorem _root_.solution : ∀ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing R] (M : Submodule R A) (s : Set R), Ideal.span s = ⊤ → (∀ g ∈ s, ∃ E : Finset A, ∀ b ∈ M, ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A)) → M.FG := by
  first | exact @GlobalTheory.submodule_fg_of_locally_le_fg | exact GlobalTheory.submodule_fg_of_locally_le_fg | (intros; apply GlobalTheory.submodule_fg_of_locally_le_fg <;> assumption)
end _root_.GlobalTheory.T
