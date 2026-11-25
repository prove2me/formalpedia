-- Prove2me | solution 1 for GlobalTheory.T.isProper_eighth_fibre_power_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:42.906903+00:00
-- url     : https://prove2.me/submissions/3d4db08a-4a2b-40bb-baba-31a61b5dba47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperEighthFibrePowerOver
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperEighthFibrePowerOverStatement
import Theorems.Thm_GlobalTheory_FibrePowerProper_isProper_eighth_fibre_power


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {T : Scheme.{0}} {B C : Over T} (pr : Fin 8 → (B ⟶ C)), (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a) → IsProper C.hom → IsProper B.hom := by
  first | exact @GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power | exact GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power | (intros; apply GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power <;> assumption)
end _root_.GlobalTheory.T
