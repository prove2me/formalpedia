-- Prove2me | solution 1 for GroundTheory.Arith.Iwasawa.isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:30.081799+00:00
-- url     : https://prove2.me/submissions/6d266daa-069f-4108-9a3e-9da4c22d524e

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
theorem _root_.solution : IsNoetherianRing (Lambda p) := inferInstance
end GroundTheory.Arith.Iwasawa
