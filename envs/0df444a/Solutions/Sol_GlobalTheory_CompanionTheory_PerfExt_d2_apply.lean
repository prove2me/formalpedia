-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfExt.d2_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:50.423831+00:00
-- url     : https://prove2.me/submissions/e270e80b-f5a3-4fc8-9e02-94eac637fc42

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply

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
namespace GlobalTheory.CompanionTheory.PerfExt
theorem _root_.solution {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (z : C2 F)
    {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    d2 F z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ + z T T' T''' φ (ψ ≫ χ) -
      mp F χ (z T T' T'' φ ψ) := rfl
end GlobalTheory.CompanionTheory.PerfExt
