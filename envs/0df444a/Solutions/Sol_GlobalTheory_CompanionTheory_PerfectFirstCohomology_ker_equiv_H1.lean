-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_equiv_H1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:27:22.905488+00:00
-- url     : https://prove2.me/submissions/77df6186-fb4b-44fc-bbb8-67a7d9157bfa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatQuotientOfUniversallyInjectiveStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LinearMapZeroOfInjectiveFullRankStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFreeKernelSplittingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalSplittingKernelBaseChangeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelFreeAtPrimesOfConstantRankStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelBaseChangeTowerEquivStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RetractBaseChangeKernelCompatibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuasiIsomorphismDegreeOneKernelStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CochainBaseChangeEquivalencesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniversalCoefficientDegreeZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelEquivCohomologyOfQuasiIsomorphismStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyBaseChangeOfCochainEquivsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PerfectFirstCohomologyBaseChange
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_mem_Z1_iff_cocycle
import Theorems.Thm_GlobalTheory_T_kernel_equiv_cohomology_of_quasi_isomorphism


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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfectFirstCohomology
variable {R C : Type} [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  {P₀ P₁ P₂ : Type} [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
  (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F)
variable {F a₀ a₁ ψ₀ ψ₁ ψ₂}
namespace GlobalTheory.CompanionTheory.PerfectFirstCohomology
theorem _root_.solution (c0 : ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀) (c1 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁)
    (d : (P₁ ⧸ LinearMap.range a₀) →ₗ[R] P₂) (hdπ : d ∘ₗ (LinearMap.range a₀).mkQ = a₁)
    (hp : QIsoAt a₀ a₁ (d0 F) (d1 F) ψ₁) : Nonempty (LinearMap.ker d ≃ₗ[R] H1 F) := by
  refine GlobalTheory.T.kernel_equiv_cohomology_of_quasi_isomorphism R P₀ P₁ P₂ (P₁ ⧸ LinearMap.range a₀) _ _ _ a₀ a₁
    (LinearMap.range a₀).mkQ d (GlobalTheory.CatCoh.Z1 F)
    (LinearMap.codRestrict _ (GlobalTheory.CatCoh.d0 F) (GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne F))
    (GlobalTheory.CatCoh.d1 F) ψ₁ ψ₀ (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range a₀) hdπ
    (GlobalTheory.CompanionTheory.PerfectFirstCohomology.mem_Z1_iff_cocycle F) ?_ (fun y => LinearMap.congr_fun c0 y) ?_
  · intro x hx
    rw [← LinearMap.comp_apply (GlobalTheory.CatCoh.d1 F) ψ₁, ← c1, LinearMap.comp_apply, hx, map_zero]
  · rwa [LinearMap.subtype_comp_codRestrict]
end GlobalTheory.CompanionTheory.PerfectFirstCohomology
