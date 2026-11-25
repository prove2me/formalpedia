-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.isPullO_over_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:32:30.217737+00:00
-- url     : https://prove2.me/submissions/b7e18087-64b8-4c7d-b794-054750487b2c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
import Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_isPullO_comp

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution {Y Z T : Over (Sp R)} (f : Y ⟶ Z) (g : Z ⟶ T) {a : HO1 T.hom} {a' : HO1 Z.hom}
    {a'' : HO1 Y.hom} (p : IsPullO (wOver g) a a') (p' : IsPullO (wOver f) a' a'') :
    IsPullO (wOver (f ≫ g)) a a'' :=
  isPullO_comp (wOver g) (wOver f) (wOver (f ≫ g)) p p'
end GlobalTheory.CompanionTheory.HopfSys
