-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OneFormCoh.muMap_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:25:57.851369+00:00
-- url     : https://prove2.me/submissions/611396d6-2d60-44de-8027-5c996c9d9d6c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtendedFormNaturality

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OneFormCoh
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.OneFormCoh
theorem _root_.solution (f : Z1 F) (v : Glob1 F) {T T' : C} (φ : T ⟶ T') :
    muMap F (f ⊗ₜ v) T T' φ = f.1 T T' φ • v.1 T' := rfl
end GlobalTheory.CompanionTheory.OneFormCoh
