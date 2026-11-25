-- Prove2me | solution 1 for GlobalTheory.T.unitaryGlModule_level_sum_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:34:30.386189+00:00
-- url     : https://prove2.me/submissions/3c3a71f0-6978-41c2-9277-e0423faaf533

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleLevelSumNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleLevelSumNormSqLeStatement
import Theorems.Thm_GlobalTheory_lev_gl_size


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv b : ℝ) (w : M), IsMod ε E μ → Shape ε kk μ bv → bv ≤ b → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∑ a, ∑ c, ‖E a c w‖ ^ 2 ≤ b ^ 4 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.lev_gl_size | exact GlobalTheory.lev_gl_size | (intros; apply GlobalTheory.lev_gl_size <;> assumption)
end _root_.GlobalTheory.T
