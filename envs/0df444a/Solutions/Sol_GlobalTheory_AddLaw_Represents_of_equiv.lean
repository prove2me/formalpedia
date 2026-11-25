-- Prove2me | solution 1 for GlobalTheory.AddLaw.Represents.of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:25:17.41515+00:00
-- url     : https://prove2.me/submissions/c4ea461f-96ed-42de-bec0-e603e120c10b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero

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
theorem _root_.solution {T U : Fin 3 → F} {p : W.toAffine.Point} (h : Represents W U p)
    (e : T ≈ U) : Represents W T p :=
  ⟨(nonsingular_of_equiv e).mpr h.left, (Point.toAffine_of_equiv e).trans h.right⟩
end Represents
end GlobalTheory.AddLaw
