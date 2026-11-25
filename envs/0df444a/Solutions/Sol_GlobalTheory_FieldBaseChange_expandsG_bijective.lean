-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.expandsG_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:07:27.086166+00:00
-- url     : https://prove2.me/submissions/35174232-0966-4fe0-a4b2-6e71a974e072

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Theorems.Thm_GlobalTheory_FieldBaseChange_noetherianSpace_generic
import Theorems.Thm_GlobalTheory_FieldBaseChange_expands_iff
import Theorems.Thm_GlobalTheory_FieldBaseChange_expandsG_iff
import Theorems.Thm_GlobalTheory_FieldBaseChange_graph_bijective
import Theorems.Thm_GlobalTheory_FieldBaseChange_isExtension_famPull
import Theorems.Thm_GlobalTheory_FieldBaseChange_isExtension_pullOver
import Theorems.Thm_GlobalTheory_FieldBaseChange_isExtension_termPull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (h : U.ExpBij k) :
    (∀ v : GroupSec U F k, ∃! s, U.ExpandsG F k v s) ∧ ∀ s, ∃! v : GroupSec U F k, U.ExpandsG F k v s :=
  have : NoetherianSpace ((Over.pullback (jK R)).obj G).left := noetherianSpace_generic U
  graph_bijective (expansionPairs U k) (genericSec U k) (genericTerm D k) (extendSec U F k)
    (isExtension_pullOver (isPullback_groupBase F) U.LG.isLB _ _) (termPull D.toPre (FractionRing R) F k)
    (isExtension_termPull D.toPre _ F k) (famPull D.toPre _ F hG k) (isExtension_famPull D.toPre _ F hG hk)
    (famProj D.toPre _ k) (famProj D.toPre F k) (fun _ _ => rfl) _ (expands_iff U k) h _ (expandsG_iff U F k)
end GlobalTheory.FieldBaseChange
