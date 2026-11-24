-- Prove2me | solution 1 for GlobalTheory.Phase.GaussSum.quat_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:25:59.469795+00:00
-- url     : https://prove2.me/submissions/e3d14b76-846f-4774-8bdb-a62eb9d05e95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.GaussSum
namespace GlobalTheory.Phase.GaussSum
theorem _root_.solution {M : Type} [AddCommGroup M] (a b c d : ℤ) (x y : Fin 4 → M) :
    quat a b c d (x + y) = quat a b c d x + quat a b c d y := by
  funext i
  fin_cases i <;> simp [quat] <;> module
end GlobalTheory.Phase.GaussSum
