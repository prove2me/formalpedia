-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.secA_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:39:26.014412+00:00
-- url     : https://prove2.me/submissions/6152ae2b-c025-4fa6-85f0-c5bf44f920c4

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
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (p : Pair φ) (x : Sec s p.1.2.1) :
    secA h p x = secPull s s' p x := rfl
end GlobalTheory.CompanionTheory.HopfSys
