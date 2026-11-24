-- Prove2me | solution 1 for GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:15.060841+00:00
-- url     : https://prove2.me/submissions/5ddb9a1e-0eb6-4ddf-ae59-679876d9b49c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedWeierstrassPTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedWeierstrassPTorsionStatement
import Theorems.Thm_GlobalTheory_WpFam_AddCharZMod_main
import Theorems.Thm_GlobalTheory_WpFam_ExpP_main
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
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wp N x) (cP N x) := by
  first | exact @GlobalTheory.WpFam.ExpP.main | exact GlobalTheory.WpFam.ExpP.main | (intros; apply GlobalTheory.WpFam.ExpP.main <;> assumption)
end _root_.GlobalTheory.T
