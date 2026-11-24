-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfExt.ext0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:09.853783+00:00
-- url     : https://prove2.me/submissions/5ef19c50-c27a-4617-8562-17d78c606849

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfExt_Ext_pi

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfExt
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} R'} [Finite C] [∀ T T' : C, Finite (T ⟶ T')]
namespace GlobalTheory.CompanionTheory.PerfExt
theorem _root_.solution (m : BC F F') : Ext R R' (fun (f : C0 F) T ↦ m.α T (f T) : C0 F → C0 F') :=
  Ext.pi (fun T b ↦ m.α T b) fun T ↦ m.bij T
end GlobalTheory.CompanionTheory.PerfExt
