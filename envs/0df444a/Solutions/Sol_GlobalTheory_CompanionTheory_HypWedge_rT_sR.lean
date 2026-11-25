-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.rT_sR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:59:23.572795+00:00
-- url     : https://prove2.me/submissions/5a6475d3-2d5f-4d9b-b9c9-6b7d8512783a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero

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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HypWedge
theorem _root_.solution (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F) (hτ : ∀ v, H1.mk F (cechDeRhamTotalCocyclesOne.fn F (τ v)) = v) (u : H1 F ⊗[R] Glob1 F) :
    LinearMap.rTensor (Glob1 F) (H1.mk F) (sR τ u) = u := by
  rw [sR, ← LinearMap.rTensor_comp_apply]
  have : H1.mk F ∘ₗ cechDeRhamTotalCocyclesOne.fn F ∘ₗ τ = LinearMap.id := LinearMap.ext hτ
  rw [this, LinearMap.rTensor_id]
  rfl
end GlobalTheory.CompanionTheory.HypWedge
