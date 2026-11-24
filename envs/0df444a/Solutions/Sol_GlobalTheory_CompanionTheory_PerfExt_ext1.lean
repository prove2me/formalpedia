-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfExt.ext1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:44:41.64682+00:00
-- url     : https://prove2.me/submissions/d122a4d3-7e39-4765-b53c-0411e837c7d9

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
theorem _root_.solution (m : BC F F') : Ext R R' (fun (f : C1 F) T T' φ ↦ m.α T' (f T T' φ) : C1 F → C1 F') :=
  Ext.pi (Q := fun T ↦ ∀ (T' : C) (_ : T ⟶ T'), F'.obj T')
    (fun T (g : ∀ (T' : C) (_ : T ⟶ T'), F.obj T') T' φ ↦ m.α T' (g T' φ)) fun T ↦
  Ext.pi (Q := fun T' ↦ ∀ (_ : T ⟶ T'), F'.obj T')
    (fun T' (g : ∀ (_ : T ⟶ T'), F.obj T') φ ↦ m.α T' (g φ)) fun T' ↦
  Ext.pi (fun _ b ↦ m.α T' b) fun _ ↦ m.bij T'
end GlobalTheory.CompanionTheory.PerfExt
