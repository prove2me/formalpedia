-- Prove2me | solution 1 for GlobalTheory.T.quasi_isomorphism_degree_one_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:47:51.077398+00:00
-- url     : https://prove2.me/submissions/ac75ebba-afdb-4fe0-a89d-736c9b5f1c64

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuasiIsomorphismDegreeOneKernel
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuasiIsomorphismDegreeOneKernelStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomologyUniversal_univ_coeff


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
theorem _root_.solution : ∀ (R A₀ A₁ A₂ P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] (d₀ : A₀ →ₗ[R] A₁) (d₁ : A₁ →ₗ[R] A₂) (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] A₀) (ψ₁ : P₁ →ₗ[R] A₁) (ψ₂ : P₂ →ₗ[R] A₂) (r : P₂ →ₗ[R] P₁) (Z : Submodule R A₁) (dZ : A₀ →ₗ[R] Z), (∀ z, z ∈ Z ↔ d₁ z = 0) → (∀ y, (dZ y : A₁) = d₀ y) → a₁ ∘ₗ a₀ = 0 → ψ₁ ∘ₗ a₀ = d₀ ∘ₗ ψ₀ → ψ₂ ∘ₗ a₁ = d₁ ∘ₗ ψ₁ → a₁ ∘ₗ r ∘ₗ a₁ = a₁ → (∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (a₀.lTensor M) (a₁.lTensor M) (d₀.lTensor M) (d₁.lTensor M) (ψ₁.lTensor M)) → ∀ (M : Type) [AddCommGroup M] [Module R M], (∀ x : M ⊗[R] A₁, d₁.lTensor M x = 0 → ∃ (t : M ⊗[R] Z) (y : M ⊗[R] A₀), Z.subtype.lTensor M t + d₀.lTensor M y = x) ∧ (∀ (t : M ⊗[R] Z) (y : M ⊗[R] A₀), Z.subtype.lTensor M t = d₀.lTensor M y → ∃ y' : M ⊗[R] A₀, dZ.lTensor M y' = t) := by
  first | exact @GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal.univ_coeff | exact GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal.univ_coeff | (intros; apply GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal.univ_coeff <;> assumption)
end _root_.GlobalTheory.T
