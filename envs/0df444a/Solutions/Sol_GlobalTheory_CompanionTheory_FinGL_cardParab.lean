-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGL.cardParab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:05:23.79293+00:00
-- url     : https://prove2.me/submissions/eee6816a-7530-4bda-8543-1e10a690a57d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_card_GL_int
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_card_parab
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGL_choose_blocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGL
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.FinGL
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.CardParab := by
  intro K _ _ _ ι _ _
  exact ⟨card_GL_int K ι, fun s b => ⟨card_parab K b, choose_blocks b⟩⟩
end GlobalTheory.CompanionTheory.FinGL
