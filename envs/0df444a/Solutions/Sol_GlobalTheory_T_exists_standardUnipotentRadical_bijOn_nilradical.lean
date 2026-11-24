-- Prove2me | solution 1 for GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:21:57.523832+00:00
-- url     : https://prove2.me/submissions/238f0ef8-6298-4f9c-b0e1-fd07430fe92f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsStandardUnipotentRadicalBijOnNilradicalStatement
import Theorems.Thm_GlobalTheory_CuspGL_UnipNilRad_exists_unip_bijOn_nilRad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (d a : ℕ), a ≤ d → ∃ (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F)), Module.finrank F A = a ∧ (H : Set (GL (Fin d) F)) = {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)} ∧ Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1) (H : Set (GL (Fin d) F)) (nilRad A) := by
  first | exact @GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad | exact GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad | (intros; apply GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad <;> assumption)
end _root_.GlobalTheory.T
