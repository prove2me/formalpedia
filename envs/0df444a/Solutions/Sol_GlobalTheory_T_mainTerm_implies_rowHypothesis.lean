-- Prove2me | solution 1 for GlobalTheory.T.mainTerm_implies_rowHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:32.257064+00:00
-- url     : https://prove2.me/submissions/9b18e43c-0144-4301-ab45-40e23c6fba1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MainTermImpliesRowHypothesis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MainTermImpliesRowHypothesisStatement
import Theorems.Thm_GlobalTheory_mainTerm_to_rowHypothesis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.MtoHM := by
  first | exact @GlobalTheory.mainTerm_to_rowHypothesis | exact GlobalTheory.mainTerm_to_rowHypothesis | (intros; apply GlobalTheory.mainTerm_to_rowHypothesis <;> assumption)
end _root_.GlobalTheory.T
