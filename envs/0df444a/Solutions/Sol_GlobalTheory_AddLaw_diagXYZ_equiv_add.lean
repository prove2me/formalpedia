-- Prove2me | solution 1 for GlobalTheory.AddLaw.diagXYZ_equiv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:56:10.504929+00:00
-- url     : https://prove2.me/submissions/da4d0cab-db9e-42c3-819a-b5b50566ac1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_proportional_diagXYZ_addXYZ
import Theorems.Thm_GlobalTheory_AddLaw_equiv_of_proportional
import Theorems.Thm_GlobalTheory_AddLaw_addXYZ_ne_zero_iff
import Theorems.Thm_GlobalTheory_AddLaw_diagXYZ_equiv_add_of_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
open GlobalTheory GlobalTheory.AddLaw
variable {F : Type*} [Field F] {W : Projective F}
namespace GlobalTheory.AddLaw
theorem _root_.solution {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : diagXYZ W P Q ≠ 0) : diagXYZ W P Q ≈ W.add P Q := by
  by_cases e : P ≈ Q
  · exact diagXYZ_equiv_add_of_equiv hP.left e
  · rw [add_of_not_equiv e]
    exact equiv_of_proportional (proportional_diagXYZ_addXYZ hP.left hQ.left) h <|
      (addXYZ_ne_zero_iff hP hQ).mpr e
end GlobalTheory.AddLaw
