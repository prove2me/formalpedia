-- Prove2me | solution 1 for GlobalTheory.BadShare.ZCalc.op_zc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:15.547955+00:00
-- url     : https://prove2.me/submissions/5e19d32c-2b62-4a7d-8e2f-8a94510b3faa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Theorems.Thm_PI_CharIdemW_act_charIdem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.ZCalc
variable {G : Type} [Group G] [Fintype G]
namespace GlobalTheory.BadShare.ZCalc
theorem _root_.solution (V W : FDRep ℂ G) :
    op W.ρ (zc V.character) = PI.CharIdem.act W (PI.CharIdem.charIdem V) := by
  rw [PI.CharIdemW.act_charIdem]
  simp only [op, zc, FDRep.char_one]
end GlobalTheory.BadShare.ZCalc
