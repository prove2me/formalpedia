-- Prove2me | solution 1 for GlobalTheory.SylvesterInertia.inrMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:59:58.309151+00:00
-- url     : https://prove2.me/submissions/c98183d0-aaf9-47ba-8d97-a8b2dd5afd98

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSignatureFstUniqueSylvester

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SylvesterInertia
open Matrix Module
open scoped ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.SylvesterInertia
theorem _root_.solution (a b : ℕ) : Function.Injective (inrMap a b) := by
  intro z z' h; funext i; exact congrFun h (Sum.inr i)
end GlobalTheory.SylvesterInertia
