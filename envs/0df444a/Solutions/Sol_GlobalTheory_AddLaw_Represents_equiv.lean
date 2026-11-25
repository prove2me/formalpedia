-- Prove2me | solution 1 for GlobalTheory.AddLaw.Represents.equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:25:09.925956+00:00
-- url     : https://prove2.me/submissions/7a76fb77-074c-4d44-909e-3f2cd3fc79e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm

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
namespace Represents
theorem _root_.solution {T U : Fin 3 → F} {p : W.toAffine.Point} (hT : Represents W T p)
    (hU : Represents W U p) : T ≈ U := by
  classical
  have h : (⟨(nonsingularLift_iff T).mpr hT.left⟩ : W.Point) =
      ⟨(nonsingularLift_iff U).mpr hU.left⟩ :=
    (Point.toAffineAddEquiv W).injective (hT.right.trans hU.right.symm)
  exact Quotient.exact (congrArg Point.point h)
end Represents
end GlobalTheory.AddLaw
