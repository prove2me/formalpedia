-- Prove2me | solution 1 for GlobalTheory.AnArc.perFactor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:34.323889+00:00
-- url     : https://prove2.me/submissions/961cc2be-c84b-4530-bab0-d5d168205eef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Theorems.Thm_GlobalTheory_AnArc_ah_ne_zero


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
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (w : ℂ) (la : A.La) (v : A.V) : A.perFactor w la v ≠ 0 :=
  mul_ne_zero (A.ah_ne_zero _ _)
    (inv_ne_zero (mul_ne_zero (mul_ne_zero (A.psi _).ne_zero (e_ne_zero _)) (e_ne_zero _)))
end GlobalTheory.AnArc
