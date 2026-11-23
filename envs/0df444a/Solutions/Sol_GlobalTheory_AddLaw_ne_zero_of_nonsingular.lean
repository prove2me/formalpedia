-- Prove2me | solution 1 for GlobalTheory.AddLaw.ne_zero_of_nonsingular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:27.745805+00:00
-- url     : https://prove2.me/submissions/d9b5072c-f891-4426-9d81-f23269d0f1ad

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
theorem _root_.solution {P : Fin 3 → F} (hP : W.Nonsingular P) : P ≠ 0 := by
  rintro rfl
  exact Y_ne_zero_of_Z_eq_zero hP rfl rfl
end GlobalTheory.AddLaw
