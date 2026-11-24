-- Prove2me | solution 1 for GlobalTheory.WeilM.SB_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:52.272799+00:00
-- url     : https://prove2.me/submissions/3966eabc-1ffc-4f40-a5be-19e205cdcf44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
namespace GlobalTheory.WeilM
theorem _root_.solution (X : Type) [TopologicalSpace X] : SB X = GlobalTheory.SplitWeil.SB X := rfl
end GlobalTheory.WeilM
