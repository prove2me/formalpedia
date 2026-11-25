-- Prove2me | solution 1 for MainStatements.Hodge.Pf.AXO.pO_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:57.100791+00:00
-- url     : https://prove2.me/submissions/461404ec-62b2-4de7-a2cf-705ba6ee7296

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
import Theorems.Thm_GlobalTheory_CechDR_IsPullO_eq_pullHO1
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
theorem _root_.solution {Y Z : Over (Sp R)} (f : Y ⟶ Z) (c : HO1 Z.hom) (c' : HO1 Y.hom) :
    IsPullO (wOver f) c c' ↔ c' = pO f c :=
  ⟨fun e ↦ e.eq_pullHO1, fun e ↦ e ▸ isPullO_pullHO1 _ c⟩
end MainStatements.Hodge.Pf.AXO
