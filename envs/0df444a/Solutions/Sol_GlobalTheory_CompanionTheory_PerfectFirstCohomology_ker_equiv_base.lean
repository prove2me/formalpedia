-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_equiv_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:02.68081+00:00
-- url     : https://prove2.me/submissions/4f162934-2674-48b0-9cee-31bb92ac5889

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
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_qiso_transport
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_mem_Z1_iff_cocycle
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_T_kernel_equiv_cohomology_of_quasi_isomorphism
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



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
theorem _root_.solution {k : Type} [CommRing k] [Algebra R k] (G : C ⥤ CommAlgCat.{0} k)
    (E₀ : k ⊗[R] C0 F ≃ₗ[k] C0 G) (E₁ : k ⊗[R] C1 F ≃ₗ[k] C1 G) (E₂ : k ⊗[R] C2 F ≃ₗ[k] C2 G)
    (h01 : ∀ x, E₁ ((d0 F).baseChange k x) = d0 G (E₀ x)) (h12 : ∀ x, E₂ ((d1 F).baseChange k x) = d1 G (E₁ x))
    (c0 : ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀) (c1 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁)
    (d : (P₁ ⧸ LinearMap.range a₀) →ₗ[R] P₂) (hdπ : d ∘ₗ (LinearMap.range a₀).mkQ = a₁)
    (hq : QIsoAt (a₀.lTensor k) (a₁.lTensor k) ((d0 F).lTensor k) ((d1 F).lTensor k) (ψ₁.lTensor k)) :
    Nonempty (LinearMap.ker (d.baseChange k) ≃ₗ[k] H1 G) := by
  refine GlobalTheory.T.kernel_equiv_cohomology_of_quasi_isomorphism k (k ⊗[R] P₀) (k ⊗[R] P₁) (k ⊗[R] P₂)
    (k ⊗[R] (P₁ ⧸ LinearMap.range a₀)) _ _ _ (a₀.baseChange k) (a₁.baseChange k)
    ((LinearMap.range a₀).mkQ.baseChange k) (d.baseChange k) (GlobalTheory.CatCoh.Z1 G)
    (LinearMap.codRestrict _ (GlobalTheory.CatCoh.d0 G) (GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne G))
    (GlobalTheory.CatCoh.d1 G) (E₁.toLinearMap ∘ₗ ψ₁.baseChange k) (E₀.toLinearMap ∘ₗ ψ₀.baseChange k)
    ?_ ?_ ?_ (GlobalTheory.CompanionTheory.PerfectFirstCohomology.mem_Z1_iff_cocycle G) ?_ ?_ ?_
  · rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective k (Submodule.mkQ_surjective _)
  · rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact k (LinearMap.exact_map_mkQ_range a₀) (Submodule.mkQ_surjective _)
  · rw [← LinearMap.baseChange_comp, hdπ]
  · intro x hx
    have h := LinearMap.congr_fun (congrArg (LinearMap.baseChange k) c1) x
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply, hx,
      map_zero] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h12, ← h, map_zero]
  · intro y
    have h := LinearMap.congr_fun (congrArg (LinearMap.baseChange k) c0) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.codRestrict_apply]
    rw [h, h01]
  · rw [LinearMap.subtype_comp_codRestrict]
    exact GlobalTheory.CompanionTheory.PerfectFirstCohomology.qiso_transport hq (AddEquiv.refl _) (AddEquiv.refl _) (AddEquiv.refl _)
      E₀.toAddEquiv E₁.toAddEquiv E₂.toAddEquiv
      (fun y => congrFun (LinearMap.baseChange_eq_ltensor a₀) y)
      (fun x => congrFun (LinearMap.baseChange_eq_ltensor a₁) x)
      (fun y => (h01 y).symm.trans (congrArg E₁ (congrFun (LinearMap.baseChange_eq_ltensor _) y)))
      (fun x => (h12 x).symm.trans (congrArg E₂ (congrFun (LinearMap.baseChange_eq_ltensor _) x)))
      (fun x => congrArg E₁ (congrFun (LinearMap.baseChange_eq_ltensor ψ₁) x))
end GlobalTheory.CompanionTheory.PerfectFirstCohomology
