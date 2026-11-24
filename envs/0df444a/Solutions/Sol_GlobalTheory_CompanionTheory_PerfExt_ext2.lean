-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfExt.ext2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:03.225689+00:00
-- url     : https://prove2.me/submissions/c3a0643f-063a-4c87-a23f-ab6d3ad42208

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
theorem _root_.solution (m : BC F F') :
    Ext R R' (fun (f : C2 F) T T' T'' φ ψ ↦ m.α T'' (f T T' T'' φ ψ) : C2 F → C2 F') :=
  Ext.pi (Q := fun T ↦ ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'')
    (fun T (g : ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'') T' T'' φ ψ ↦
      m.α T'' (g T' T'' φ ψ)) fun T ↦
  Ext.pi (Q := fun T' ↦ ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'')
    (fun T' (g : ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'') T'' φ ψ ↦
      m.α T'' (g T'' φ ψ)) fun T' ↦
  Ext.pi (Q := fun T'' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'')
    (fun T'' (g : ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'') φ ψ ↦ m.α T'' (g φ ψ)) fun T'' ↦
  Ext.pi (Q := fun _ ↦ ∀ (_ : T' ⟶ T''), F'.obj T'')
    (fun φ (g : ∀ (_ : T' ⟶ T''), F.obj T'') ψ ↦ m.α T'' (g ψ)) fun _ ↦
  Ext.pi (fun _ b ↦ m.α T'' b) fun _ ↦ m.bij T''
end GlobalTheory.CompanionTheory.PerfExt
