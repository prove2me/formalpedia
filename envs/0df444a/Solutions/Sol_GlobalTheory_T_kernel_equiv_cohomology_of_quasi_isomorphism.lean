-- Prove2me | solution 1 for GlobalTheory.T.kernel_equiv_cohomology_of_quasi_isomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:40:10.238989+00:00
-- url     : https://prove2.me/submissions/c40eb178-31c0-4a77-9a5d-3e61311e6ac1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelEquivCohomologyOfQuasiIsomorphism
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelEquivCohomologyOfQuasiIsomorphismStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfKerCoh_ker_equiv_cohomology


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S P₀ P₁ P₂ T B₀ B₁ B₂ : Type) [CommRing S] [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂] [AddCommGroup T] [Module S T] [AddCommGroup B₀] [Module S B₀] [AddCommGroup B₁] [Module S B₁] [AddCommGroup B₂] [Module S B₂] (a₀ : P₀ →ₗ[S] P₁) (a₁ : P₁ →ₗ[S] P₂) (π : P₁ →ₗ[S] T) (dT : T →ₗ[S] P₂) (Z : Submodule S B₁) (dB : B₀ →ₗ[S] Z) (b₁ : B₁ →ₗ[S] B₂) (f : P₁ →ₗ[S] B₁) (ψ₀ : P₀ →ₗ[S] B₀), Function.Surjective π → Function.Exact a₀ π → dT ∘ₗ π = a₁ → (∀ z, z ∈ Z ↔ b₁ z = 0) → (∀ x, a₁ x = 0 → b₁ (f x) = 0) → (∀ y, f (a₀ y) = (dB (ψ₀ y) : B₁)) → QIsoAt a₀ a₁ (Z.subtype ∘ₗ dB) b₁ f → Nonempty (LinearMap.ker dT ≃ₗ[S] Z ⧸ LinearMap.range dB) := by
  first | exact @GlobalTheory.CompanionTheory.PerfKerCoh.ker_equiv_cohomology | exact GlobalTheory.CompanionTheory.PerfKerCoh.ker_equiv_cohomology | (intros; apply GlobalTheory.CompanionTheory.PerfKerCoh.ker_equiv_cohomology <;> assumption)
end _root_.GlobalTheory.T
