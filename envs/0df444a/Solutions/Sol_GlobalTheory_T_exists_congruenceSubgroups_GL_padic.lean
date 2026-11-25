-- Prove2me | solution 1 for GlobalTheory.T.exists_congruenceSubgroups_GL_padic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:56.061809+00:00
-- url     : https://prove2.me/submissions/2ebc2a66-67ec-4dec-98bb-6ec3f62abfdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CongruenceSubgroupsGLPadic
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CongruenceSubgroupsGLPadicStatement
import Theorems.Thm_GlobalTheory_congruenceSubgroups_GL_padic


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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n], ∃ Γ : ℕ → Subgroup (GL n ℚ_[l]), ∀ k X, X ∈ Γ k ↔ ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  first | exact @GlobalTheory.congruenceSubgroups_GL_padic | exact GlobalTheory.congruenceSubgroups_GL_padic | (intros; apply GlobalTheory.congruenceSubgroups_GL_padic <;> assumption)
end _root_.GlobalTheory.T
