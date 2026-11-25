-- Prove2me | solution 1 for GlobalTheory.AnArc.torusProj_periodZero_eq_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:25:27.811515+00:00
-- url     : https://prove2.me/submissions/b1894eb2-4849-468d-aa93-cfa62887637a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_torusProj_Pw_im
import Theorems.Thm_GlobalTheory_AnArc_torusProj_Pw_re
import Theorems.Thm_GlobalTheory_AnArc_degeneratingTori_periodMap_eq_base_of_y_eq_zero


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
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (n : A.X →+ ℤ) (l : A.abelian₂) (x : A.X) :
    A.torusProj (A.P0 (La.mk 0 n l)) x = ((n x + (A.H l (A.ct x)).im : ℝ) : ℂ) := by
  rw [← A.degeneratingTori_periodMap_eq_base_of_y_eq_zero 0 (La.mk_y 0 n l)]
  apply Complex.ext
  · rw [torusProj_Pw_re]; simp
  · rw [torusProj_Pw_im]; simp
end GlobalTheory.AnArc
