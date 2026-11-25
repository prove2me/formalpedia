-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.isPullO_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:39:56.087862+00:00
-- url     : https://prove2.me/submissions/8cc7e6e7-d6b9-4db7-91e1-e4a8d792eb75

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo

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
theorem _root_.solution {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
    {h : φ ≫ s = s' ≫ spMap (RingHom.id R)} {a b : HO1 s} {a' b' : HO1 s'} (ha : IsPullO h a a')
    (hb : IsPullO h b b') : IsPullO h (a - b) (a' - b') := by
  unfold IsPullO at *; rw [map_sub, map_sub, ha, hb]
end GlobalTheory.CompanionTheory.HopfSys
