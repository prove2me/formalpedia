-- Prove2me | solution 1 for GlobalTheory.Doubling.conj_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:39:14.372807+00:00
-- url     : https://prove2.me/submissions/52928a79-fc98-40ee-be39-9c102b40524e

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
variable {H : Type} {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
namespace GlobalTheory.Doubling
theorem _root_.solution (π : H → X → X) (x y : X) (g : H) : starRingEnd ℂ (coef π x y g) = inner ℂ (π g x) y :=
  inner_conj_symm _ _
end GlobalTheory.Doubling
