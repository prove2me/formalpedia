-- Prove2me | solution 1 for GlobalTheory.Nef.PolesOfT.one_le_Mx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:01:58.238857+00:00
-- url     : https://prove2.me/submissions/e377ca07-4bd6-4443-bf43-64dbc8908011

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsManyBoundedByPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PolesOfT
open Polynomial
variable {k F : Type} [Field k] [Field F] [Algebra k F]
namespace GlobalTheory.Nef.PolesOfT
theorem _root_.solution (t : F) (v : Place k F) : 1 ≤ Mx t v := le_max_left _ _
end GlobalTheory.Nef.PolesOfT
