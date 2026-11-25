-- Prove2me | solution 1 for GlobalTheory.SS.ampleCub_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:27.183156+00:00
-- url     : https://prove2.me/submissions/71959733-0bbb-4bbf-b57a-019e8791184e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Theorems.Thm_GlobalTheory_SS_linComb_triv_gen
import Theorems.Thm_GlobalTheory_AbLaw_pw_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SS
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
namespace GlobalTheory.SS
theorem _root_.solution {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsAffine G.left] :
    AmpleCub G (Inh.trivLB G.left) := by
  unfold AmpleCub
  refine ⟨Inh.trivLB_isLB _, linComb_triv_gen _ _, linComb_triv_gen _ _, 1, le_rfl, fun x => ?_⟩
  rw [Nat.cast_one, pw_one]
  refine ⟨oneSec _, ?_, ?_⟩
  · rw [nonzeroLocus_oneSec]
    trivial
  · rw [nonzeroLocus_oneSec]
    exact isAffineOpen_top _
end GlobalTheory.SS
