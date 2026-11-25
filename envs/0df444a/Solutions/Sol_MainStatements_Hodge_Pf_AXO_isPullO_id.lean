-- Prove2me | solution 1 for MainStatements.Hodge.Pf.AXO.isPullO_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:54:33.817019+00:00
-- url     : https://prove2.me/submissions/66449c7f-69ec-463f-a535-fa21337de880

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_CompositeRestrictionPullInjective
import Theorems.Thm_P2M_MainStatements_Hodge_Pf_AXO_isPullO_id__c9a67d2b14ee

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
theorem _root_.solution {X : Scheme.{0}} (s : X ⟶ Sp R) (φ : X ⟶ X) (hφ : φ = 𝟙 X)
    (h : φ ≫ s = s ≫ spMap (RingHom.id R)) (c : HO1 s) : IsPullO h c c := by
  subst hφ; exact isPullO_id' s h c
end MainStatements.Hodge.Pf.AXO
