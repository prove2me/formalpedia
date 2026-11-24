-- Prove2me | solution 1 for GlobalTheory.AddLaw.diagXYZ_ne_zero_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:56:31.975266+00:00
-- url     : https://prove2.me/submissions/f9a53d68-d764-4ae2-984b-3e62eeeee251

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_ne_zero_of_nonsingular
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
    (h : P ≈ Q) : diagXYZ W P Q ≠ 0 :=
  ne_zero_of_nonsingular <| (nonsingular_of_equiv <| diagXYZ_equiv_add_of_equiv hP.left h).mpr <|
    nonsingular_add hP hQ
end GlobalTheory.AddLaw
