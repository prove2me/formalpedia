-- Prove2me | solution 1 for GlobalTheory.AddLaw.addXYZ_ne_zero_or_diagXYZ_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:12:16.298992+00:00
-- url     : https://prove2.me/submissions/989140dc-d941-41ec-9fc6-0ea99ba62d00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_addXYZ_ne_zero_iff
import Theorems.Thm_GlobalTheory_AddLaw_diagXYZ_ne_zero_of_equiv

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
theorem _root_.solution {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : W.addXYZ P Q ≠ 0 ∨ diagXYZ W P Q ≠ 0 := by
  by_cases h : P ≈ Q
  · exact Or.inr <| diagXYZ_ne_zero_of_equiv hP hQ h
  · exact Or.inl <| (addXYZ_ne_zero_iff hP hQ).mpr h
end GlobalTheory.AddLaw
