-- Prove2me | solution 1 for GlobalTheory.AnArc.q_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:41.411808+00:00
-- url     : https://prove2.me/submissions/9e31e757-81e3-4b31-8b95-5e3cf0452115

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
theorem _root_.solution (μ ν : A.X) : A.q (μ + ν) = A.q μ + A.q ν + A.be μ ν := by
  have h1 := A.two_mul_q (μ + ν)
  have h2 := A.two_mul_q μ
  have h3 := A.two_mul_q ν
  simp only [map_add, LinearMap.add_apply, A.be_symm ν μ] at h1
  omega
end GlobalTheory.AnArc
