-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominatorsReal.cm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:45:38.42705+00:00
-- url     : https://prove2.me/submissions/8f920dd5-6c61-46e8-b0a7-c0d6e693d501

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ZetaValueIdeals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
namespace ZetaDenominatorsReal
theorem _root_.solution (h : ZetaDenominatorsReal) : ZetaDenominators :=
  fun E _ _ _ s hs => h (maximalRealSubfield E) s hs
end ZetaDenominatorsReal
end GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
