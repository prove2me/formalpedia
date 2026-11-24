-- Prove2me | solution 1 for GroundTheory.Arith.Iwasawa.IsDistinguished.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:45:02.605999+00:00
-- url     : https://prove2.me/submissions/a89d8229-97ff-4221-8ed0-a109b4264c26

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
variable {p}


theorem solution {P : ℤ_[p][X]} (hP : IsDistinguished p P) : P ≠ 0 := by
  exact hP.monic.ne_zero
