-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOn.twCoord_twZeroEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:07:37.196908+00:00
-- url     : https://prove2.me/submissions/1ef04714-6cc5-4ba5-b867-92d0edbac849

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_coord_congr
import Theorems.Thm_GlobalTheory_AbLaw_isLB_tw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
open GlobalTheory.AbLaw.SecOn
open GlobalTheory.LB
variable {L M H : LB X} {V W : X.Opens}
variable {t : ℤ}
namespace GlobalTheory.AbLaw.SecOn
theorem _root_.solution (hM : M.IsLB) (hH : H.IsLB) (s : SecOn M V) (p : M.ι) (k : H.ι) :
    twCoord (twZeroEquiv hM hH V s) p k = rs X (inf_le_inf_left V inf_le_left) (coord s p) := by
  have h : V ⊓ (M.U p ⊓ H.U k) ≤ M.U p ⊓ H.U k ⊓ M.U p :=
    le_inf inf_le_right (inf_le_right.trans inf_le_left)
  refine (rs_self le_rfl _).symm.trans ((coord_congr hM (isLB_tw hM hH 0) (twZeroIso M H)
    (twZeroIso_isGen hM) s (p, k) p le_rfl (inf_le_inf_left V inf_le_left) h).trans ?_)
  exact (congrArg (· * rs X (inf_le_inf_left V inf_le_left : V ⊓ (M.U p ⊓ H.U k) ≤ V ⊓ M.U p)
    (coord s p)) ((rs_rs _ h _).trans (resG_g_self hM p _))).trans (_root_.one_mul _)
end GlobalTheory.AbLaw.SecOn
