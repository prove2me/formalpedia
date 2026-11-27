-- Prove2me | solution 1 for MainStatements.Hodge.Pf.AXO.pO_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:56:30.828925+00:00
-- url     : https://prove2.me/submissions/3e3d65cd-97c6-48b9-9a9a-32a554d02e41

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
import Theorems.Thm_P2M_MainStatements_Hodge_Pf_AXO_isPullO_comp__f746c8e04720
import Theorems.Thm_MainStatements_Hodge_Pf_AXO_pO_spec
import Theorems.Thm_GlobalTheory_CechDR_isPullO_pullHO1


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
theorem _root_.solution {X Y Z : Over (Sp R)} (f : X ⟶ Y) (g : Y ⟶ Z) (c : HO1 Z.hom) :
    pO (f ≫ g) c = pO f (pO g c) :=
  ((pO_spec _ _ _).1 (isPullO_comp' (RingHom.id_comp _) (wOver g) (wOver f) (f ≫ g).left
    (Over.comp_left _ _ _ f g) (wOver (f ≫ g)) c (pO g c) (pO f (pO g c))
    (isPullO_pullHO1 _ c) (isPullO_pullHO1 _ _))).symm
end MainStatements.Hodge.Pf.AXO
