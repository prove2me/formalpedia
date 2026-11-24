-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.realTensorEvalAlgHom_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:03.540142+00:00
-- url     : https://prove2.me/submissions/04d5aacc-3332-4792-b039-bfa0ef7b78dd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjective

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  (R' : Type) [CommRing R'] [Algebra R R']
variable {R'} {M : Type} [AddCommGroup M] [Module R M] (j : M →ₗ[R] R')
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution (n : M) (f : C1 F) {T T' : C} (φ : T ⟶ T') :
    ev1 F j (n ⊗ₜ f) T T' φ = j n ⊗ₜ f T T' φ := rfl
end GlobalTheory.CompanionTheory.WedgeOf
