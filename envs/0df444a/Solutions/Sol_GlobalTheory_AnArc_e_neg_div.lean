-- Prove2me | solution 1 for GlobalTheory.AnArc.e_neg_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:53:49.545058+00:00
-- url     : https://prove2.me/submissions/bc6d2339-061d-4c45-a983-4594c62511c4

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
theorem _root_.solution (x : ℂ) : eTwoPi (-(x / (2 * Complex.I))) = Complex.exp (-(Real.pi * x)) := by
  rw [eTwoPi]; congr 1
  have := Complex.I_ne_zero
  field_simp
end GlobalTheory.AnArc
