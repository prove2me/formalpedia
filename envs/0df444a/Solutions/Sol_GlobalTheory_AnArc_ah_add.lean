-- Prove2me | solution 1 for GlobalTheory.AnArc.ah_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:40.816297+00:00
-- url     : https://prove2.me/submissions/bbd64e9c-df40-45c3-a9e7-01c0ca38d9d8

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
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (l : A.abelian₂) (z c : Fin A.gB → ℂ) :
    A.ah l (z + c) = A.ah l z * Complex.exp (Real.pi * A.H c l) := by
  rw [ah, ah, H_add_left, mul_assoc (A.chi l), ← Complex.exp_add]
  congr 2; ring
end GlobalTheory.AnArc
