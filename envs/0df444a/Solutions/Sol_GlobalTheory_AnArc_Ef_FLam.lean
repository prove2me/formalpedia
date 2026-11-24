-- Prove2me | solution 1 for GlobalTheory.AnArc.Ef_FLam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:57:36.828494+00:00
-- url     : https://prove2.me/submissions/d1b2e4ff-5bab-4d72-9068-6a7409069233

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Theorems.Thm_GlobalTheory_AnArc_H_F

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
theorem _root_.solution (a : O) (l m : A.abelian₂) : A.Ef (A.FLam a l) m = A.Ef l (A.FLam (star a) m) := by
  have h : (A.Ef (A.FLam a l) m : ℝ) = A.Ef l (A.FLam (star a) m) := by
    rw [Ef_eq_im, Ef_eq_im, coe_FLam, coe_FLam, H_F]
  exact_mod_cast h
end GlobalTheory.AnArc
