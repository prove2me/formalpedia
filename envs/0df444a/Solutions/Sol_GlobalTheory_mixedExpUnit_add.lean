-- Prove2me | solution 1 for GlobalTheory.mixedExpUnit_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:59.803196+00:00
-- url     : https://prove2.me/submissions/a48f3362-8617-4888-a754-abb12b32298a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] (x y : mixedSpace K) :
    mixedExpUnit K (x + y) = mixedExpUnit K x * mixedExpUnit K y :=
  Units.ext (Prod.ext (funext fun w => Real.exp_add (x.1 w) (y.1 w))
    (funext fun w => Complex.exp_add (x.2 w) (y.2 w)))
end GlobalTheory
