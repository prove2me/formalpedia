-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLift.spMap_comp_spMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:24:32.19791+00:00
-- url     : https://prove2.me/submissions/537e0c84-5153-4467-8082-b124d63f5875

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLift
namespace GlobalTheory.CompanionTheory.CotLift
theorem _root_.solution {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap g = spMap (h.comp g) := by
  rw [← Spec.map_comp]; rfl
end GlobalTheory.CompanionTheory.CotLift
