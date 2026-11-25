-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.Shuffle.crossZ_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:45.221224+00:00
-- url     : https://prove2.me/submissions/b98b0718-66d0-44c9-9d91-90ee772d47cb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossProductKernelQuotientVanishing

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf GlobalTheory.CompanionTheory.WedgeOf.Shuffle
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
variable (F)
namespace GlobalTheory.CompanionTheory.WedgeOf.Shuffle
theorem _root_.solution (f h : Z1 F) :
    crossZ F (f ⊗ₜ h) = cupZ (box F) ((boxL F).pullbackOneCocycle f) ((boxR F).pullbackOneCocycle h) := rfl
end GlobalTheory.CompanionTheory.WedgeOf.Shuffle
