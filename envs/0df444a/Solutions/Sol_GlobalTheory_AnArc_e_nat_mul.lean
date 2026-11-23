-- Prove2me | solution 1 for GlobalTheory.AnArc.e_nat_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:57.898989+00:00
-- url     : https://prove2.me/submissions/6ce57832-e9c4-4d22-ae25-8be4edb25599

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
theorem _root_.solution (n : ℕ) (x : ℂ) : eTwoPi (n * x) = eTwoPi x ^ n := by
  rw [eTwoPi, eTwoPi, ← Complex.exp_nat_mul]; congr 1; ring
end GlobalTheory.AnArc
