-- Prove2me | solution 1 for GlobalTheory.UnfoldNormal.shear_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:48:21.993664+00:00
-- url     : https://prove2.me/submissions/490f6dab-d56c-4285-b8f4-03c4678e20b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnfoldNormal
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
namespace GlobalTheory.UnfoldNormal
theorem _root_.solution (N : Subgroup H) : shear N = shearEquiv ∘ Prod.map Subtype.val id := rfl
end GlobalTheory.UnfoldNormal
