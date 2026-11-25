-- Prove2me | solution 2 for GroundTheory.Arith.Iwasawa.IsDistinguished.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:36.118608+00:00
-- url     : https://prove2.me/submissions/15ca00a3-8a49-4c76-85f2-48af9ed6199f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_IwasawaModules_SpanFinrankMaximalIdealLeTwo
import Theorems.Thm_GroundTheory_Arith_Iwasawa_IsDistinguished_monic

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
variable {p}
namespace GroundTheory.Arith.Iwasawa
namespace IsDistinguished
theorem _root_.solution {P : ℤ_[p][X]} (hP : IsDistinguished p P) : P ≠ 0 :=
  hP.monic.ne_zero
end IsDistinguished
end GroundTheory.Arith.Iwasawa
