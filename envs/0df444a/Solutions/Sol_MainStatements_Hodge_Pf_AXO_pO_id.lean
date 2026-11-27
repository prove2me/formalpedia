-- Prove2me | solution 1 for MainStatements.Hodge.Pf.AXO.pO_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:56:25.385796+00:00
-- url     : https://prove2.me/submissions/26be9cfb-fa90-4454-a108-7ca837606380

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
import Theorems.Thm_MainStatements_Hodge_Pf_AXO_pO_spec
import Theorems.Thm_MainStatements_Hodge_Pf_AXO_isPullO_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.AXO
variable {R : Type} [CommRing R]
namespace MainStatements.Hodge.Pf.AXO
theorem _root_.solution (Y : Over (Sp R)) (c : HO1 Y.hom) : pO (𝟙 Y) c = c :=
  ((pO_spec _ _ _).1 (isPullO_id Y.hom (𝟙 Y : Y ⟶ Y).left (Over.id_left Y) _ c)).symm
end MainStatements.Hodge.Pf.AXO
