-- Prove2me | solution 1 for GlobalTheory.AddLaw.addXYZ_equiv_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:52.431841+00:00
-- url     : https://prove2.me/submissions/6a57b081-433b-45b1-85f5-a93eae5a75c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_addXYZ_ne_zero_iff

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
    (h : W.addXYZ P Q ≠ 0) : W.addXYZ P Q ≈ W.add P Q := by
  rw [add_of_not_equiv <| (addXYZ_ne_zero_iff hP hQ).mp h]
end GlobalTheory.AddLaw
