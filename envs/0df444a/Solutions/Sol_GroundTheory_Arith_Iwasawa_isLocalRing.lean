-- Prove2me | solution 1 for GroundTheory.Arith.Iwasawa.isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:30.265722+00:00
-- url     : https://prove2.me/submissions/5213f094-57e6-41f1-8243-2c1abce26fe0

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_IwasawaModules_SpanFinrankMaximalIdealLeTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Iwasawa
open PowerSeries IsLocalRing
open scoped Polynomial
variable (p : ℕ) [hp : Fact p.Prime]
namespace GroundTheory.Arith.Iwasawa
theorem _root_.solution : IsLocalRing (Lambda p) := inferInstance
end GroundTheory.Arith.Iwasawa
