-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfExt.ext3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:35:56.845149+00:00
-- url     : https://prove2.me/submissions/c4671a8b-2886-4daf-a44e-7fa1c0c7fe75

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
    Ext R R' (fun (f : C3 F) T T' T'' T''' φ ψ χ ↦ m.α T''' (f T T' T'' T''' φ ψ χ) : C3 F → C3 F') :=
  Ext.pi (Q := fun T ↦ ∀ (T' T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T (g : ∀ (T' T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''')
      T' T'' T''' φ ψ χ ↦ m.α T''' (g T' T'' T''' φ ψ χ)) fun T ↦
  Ext.pi (Q := fun T' ↦ ∀ (T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T' (g : ∀ (T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''')
      T'' T''' φ ψ χ ↦ m.α T''' (g T'' T''' φ ψ χ)) fun T' ↦
  Ext.pi (Q := fun T'' ↦ ∀ (T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T'' (g : ∀ (T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''')
      T''' φ ψ χ ↦ m.α T''' (g T''' φ ψ χ)) fun T'' ↦
  Ext.pi (Q := fun T''' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T''' (g : ∀ (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''') φ ψ χ ↦
      m.α T''' (g φ ψ χ)) fun T''' ↦
  Ext.pi (Q := fun _ ↦ ∀ (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun φ (g : ∀ (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''') ψ χ ↦ m.α T''' (g ψ χ)) fun _ ↦
  Ext.pi (Q := fun _ ↦ ∀ (_ : T'' ⟶ T'''), F'.obj T''')
    (fun ψ (g : ∀ (_ : T'' ⟶ T'''), F.obj T''') χ ↦ m.α T''' (g χ)) fun _ ↦
  Ext.pi (fun _ b ↦ m.α T''' b) fun _ ↦ m.bij T'''
end GlobalTheory.CompanionTheory.PerfExt
