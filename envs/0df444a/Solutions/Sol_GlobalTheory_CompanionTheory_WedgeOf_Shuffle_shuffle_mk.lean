-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.Shuffle.shuffle_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:41.748068+00:00
-- url     : https://prove2.me/submissions/48b3ff67-8a05-44e7-a741-cc682db3eba9

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
namespace GlobalTheory.CompanionTheory.WedgeOf.Shuffle
theorem _root_.solution (z : C2 (box F)) {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') :
    shuffle F z (⟨a, a', φ⟩, ⟨b, b', ψ⟩) =
      z (a, b) (a', b) (a', b') (φ, 𝟙 b) (𝟙 a', ψ) - z (a, b) (a, b') (a', b') (𝟙 a, ψ) (φ, 𝟙 b') := rfl
end GlobalTheory.CompanionTheory.WedgeOf.Shuffle
