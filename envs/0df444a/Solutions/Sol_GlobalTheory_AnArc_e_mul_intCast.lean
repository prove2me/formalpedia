-- Prove2me | solution 1 for GlobalTheory.AnArc.e_mul_intCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:45.070418+00:00
-- url     : https://prove2.me/submissions/db4cb86d-2934-4bbb-a5e1-af1763ea2886

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
attribute [instance] AnArc.acg AnArc.free AnArc.fin AnArc.mod AnArc.discrete
open GlobalTheory.AnArc
namespace GlobalTheory.AnArc
theorem _root_.solution (x : ℂ) (n : ℤ) : eTwoPi (x * n) = eTwoPi x ^ n := by
  rw [eTwoPi, eTwoPi, ← Complex.exp_int_mul]; congr 1; ring
end GlobalTheory.AnArc
