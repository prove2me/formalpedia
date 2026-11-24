-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.Dual.val_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:46.88388+00:00
-- url     : https://prove2.me/submissions/0c0dc99a-619c-419c-9f6e-d9d78e67e648

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnramifiedQuadraticLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianDualInvAlgBaseChangeUnramifiedIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.Dual
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
namespace GlobalTheory.UnitLemma.Unr.Dual
theorem _root_.solution (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy)]
  ring
end GlobalTheory.UnitLemma.Unr.Dual
