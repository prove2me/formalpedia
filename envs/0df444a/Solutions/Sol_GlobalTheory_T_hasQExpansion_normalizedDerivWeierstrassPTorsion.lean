-- Prove2me | solution 1 for GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:33.179109+00:00
-- url     : https://prove2.me/submissions/25f195f3-b143-4e14-b45b-e1ea161826e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedDerivWeierstrassPTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionNormalizedDerivWeierstrassPTorsionStatement
import Theorems.Thm_GlobalTheory_WpFam_AddCharZMod_main
import Theorems.Thm_GlobalTheory_WpFam_DerivExpansion_main
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
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wpd N x) (cD N x) := by
  first | exact @GlobalTheory.WpFam.DerivExpansion.main | exact GlobalTheory.WpFam.DerivExpansion.main | (intros; apply GlobalTheory.WpFam.DerivExpansion.main <;> assumption)
end _root_.GlobalTheory.T
