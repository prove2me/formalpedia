-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomology.proj_coker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:17:15.038551+00:00
-- url     : https://prove2.me/submissions/1cb463d4-9b25-4db0-842a-1d119330a349

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
import Theorems.Thm_GlobalTheory_T_flat_quotient_of_universally_injective


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
namespace GlobalTheory.CompanionTheory.PerfectFirstCohomology
theorem _root_.solution (R P₀ P₁ : Type) [CommRing R] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
    [Module.Finite R P₀] [Module.Finite R P₁] [Module.Projective R P₀] [Module.Projective R P₁]
    (a₀ : P₀ →ₗ[R] P₁) (u : P₀) (hu : a₀ u = 0)
    (hU : ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] u) ∧
      ∀ x : M ⊗[R] P₀, a₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] u = x) :
    Module.Projective R (P₁ ⧸ LinearMap.range a₀) := by
  have hle : Submodule.span R {u} ≤ LinearMap.ker a₀ := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hu
  have hcomp : (Submodule.span R {u}).liftQ a₀ hle ∘ₗ (Submodule.span R {u}).mkQ = a₀ :=
    Submodule.liftQ_mkQ _ _ _
  have hflat : Module.Flat R (P₁ ⧸ LinearMap.range ((Submodule.span R {u}).liftQ a₀ hle)) := by
    apply GlobalTheory.T.flat_quotient_of_universally_injective
    intro M _ _
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective M (Submodule.mkQ_surjective (Submodule.span R {u})) z
    have hx : a₀.lTensor M x = 0 := by
      rw [← hcomp, LinearMap.lTensor_comp_apply]
      exact hz
    obtain ⟨m, rfl⟩ := (hU M).2 x hx
    rw [LinearMap.lTensor_tmul, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self u), TensorProduct.tmul_zero]
  rw [Submodule.range_liftQ] at hflat
  haveI := hflat
  haveI : Module.FinitePresentation R P₁ := Module.finitePresentation_of_projective R P₁
  haveI : Module.FinitePresentation R (P₁ ⧸ LinearMap.range a₀) :=
    Module.finitePresentation_of_surjective (LinearMap.range a₀).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map a₀)
  exact Module.Flat.projective_of_finitePresentation
end GlobalTheory.CompanionTheory.PerfectFirstCohomology
