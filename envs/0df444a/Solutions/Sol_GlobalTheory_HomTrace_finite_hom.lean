-- Prove2me | solution 1 for GlobalTheory.HomTrace.finite_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:42:26.377291+00:00
-- url     : https://prove2.me/submissions/9e656bea-2724-47bc-bb92-f39f5ff063ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TraceEqFinrankMulSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.HomTrace
namespace GlobalTheory.HomTrace
theorem _root_.solution (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Module.Finite ℂ (X →+ ℂ) :=
  Module.Finite.equiv (addMonoidHomLequivInt (A := X) (B := ℂ) ℂ).symm
end GlobalTheory.HomTrace
