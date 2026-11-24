-- Prove2me | solution 1 for GlobalTheory.T.weierstrass_division_value_q_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:21.386313+00:00
-- url     : https://prove2.me/submissions/4b8cb117-1f95-4f80-8672-8cf9344bda8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassDivisionValueQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassDivisionValueQExpansionStatement
import Theorems.Thm_GlobalTheory_WpFam_AddCharZMod_main
import Theorems.Thm_GlobalTheory_WpFam_ExpansionB_main
import Theorems.Thm_GlobalTheory_WpFam_RowsSummed_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), x ≠ 0 → HasQ N (wB N x) (cB N x) := by
  first | exact @GlobalTheory.WpFam.ExpansionB.main | exact GlobalTheory.WpFam.ExpansionB.main | (intros; apply GlobalTheory.WpFam.ExpansionB.main <;> assumption)
end _root_.GlobalTheory.T
