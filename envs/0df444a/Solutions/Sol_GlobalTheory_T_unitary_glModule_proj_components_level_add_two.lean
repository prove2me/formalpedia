-- Prove2me | solution 1 for GlobalTheory.T.unitary_glModule_proj_components_level_add_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:25.33786+00:00
-- url     : https://prove2.me/submissions/49660228-5d30-44ea-a56e-710fef7d9c59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleProjComponentsLevelAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleProjComponentsLevelAddTwoStatement
import Theorems.Thm_GlobalTheory_lev_io_pr_single


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
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (j : ℕ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → Lev ε E μ j w → ∀ s c d, Lev ε E μ (j + 2) (io s (pr s (Pi.single c w)) d) := by
  first | exact @GlobalTheory.lev_io_pr_single | exact GlobalTheory.lev_io_pr_single | (intros; apply GlobalTheory.lev_io_pr_single <;> assumption)
end _root_.GlobalTheory.T
