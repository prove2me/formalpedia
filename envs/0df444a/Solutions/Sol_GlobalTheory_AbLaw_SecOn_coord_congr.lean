-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOn.coord_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:36:57.858513+00:00
-- url     : https://prove2.me/submissions/07301e2d-b4fd-4cb2-a864-8eaafae0b6d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_LB_coord_isoOfGen_hom_app


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
namespace GlobalTheory.AbLaw.SecOn
theorem _root_.solution (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen) (s : SecOn L V)
    (p : M.ι) (q : L.ι) {O : X.Opens} (hp : O ≤ V ⊓ M.U p) (hq : O ≤ V ⊓ L.U q)
    (h : O ≤ M.U p ⊓ L.U q) :
    rs X hp (coord (congr hL hM w hw V s) p) =
      rs X h (show Γ(X, M.U p ⊓ L.U q)ˣ from w.s (p, q)).val * rs X hq (coord s q) :=
  coord_isoOfGen_hom_app hL hM w hw s p q hp hq h
end GlobalTheory.AbLaw.SecOn
