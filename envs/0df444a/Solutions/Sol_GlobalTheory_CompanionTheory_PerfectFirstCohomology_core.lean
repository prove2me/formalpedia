-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomology.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:46:24.705395+00:00
-- url     : https://prove2.me/submissions/78872b8f-d4d6-42c7-8be5-f7a6ead5c859

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
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_proj_coker
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_regular_of_fibres
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_stein_univ
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_qiso_lid
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_mem_Z1_iff_cocycle
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_ker_equiv_H1
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_ker_equiv_base
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_T_cochain_base_change_equivalences
import Theorems.Thm_GlobalTheory_T_first_cohomology_base_change_of_cochain_equivs
import Theorems.Thm_GlobalTheory_T_quasi_isomorphism_degree_one_kernel
import Theorems.Thm_GlobalTheory_T_universal_coefficient_degree_zero
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
theorem _root_.solution [Finite C] [∀ T T' : C, Finite (T ⟶ T')] [Module.Finite R P₀] [Module.Finite R P₁] [Module.Projective R P₀]
    [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (g : ℕ)
    (h10 : a₁ ∘ₗ a₀ = 0) (c0 : ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀) (c1 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁)
    (hq0 : ∀ (M : Type) [AddCommGroup M] [Module R M],
      QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] C0 F) ((d0 F).lTensor M) (ψ₀.lTensor M))
    (hq' : ∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (a₀.lTensor M) (a₁.lTensor M)
      ((d0 F).lTensor M) ((d1 F).lTensor M) (ψ₁.lTensor M))
    (hS : SteinU F) (hVB : VB R (H1 F) g)
    (hfib : ∀ (k : Type) [Field k] [Algebra R k], ∃ (F' : C ⥤ CommAlgCat.{0} k) (_ : BC F F'),
      Module.finrank k (H1 F') = g) : H1CommutesBaseChange F := by
  have h1zero : GlobalTheory.CatCoh.d0 F 1 = 0 := by
    funext T T' φ
    rw [GlobalTheory.CatCoh.amitsur_d0_apply]
    simp
  obtain ⟨u, hu, hU⟩ := GlobalTheory.T.universal_coefficient_degree_zero R _ _ P₀ P₁
    (GlobalTheory.CatCoh.d0 F) a₀ ψ₀ ψ₁ 1 c0 h1zero hq0
    (fun M _ _ => GlobalTheory.CompanionTheory.PerfectFirstCohomology.stein_univ R C F hS M)
  haveI : Module.Projective R (P₁ ⧸ LinearMap.range a₀) :=
    GlobalTheory.CompanionTheory.PerfectFirstCohomology.proj_coker R P₀ P₁ a₀ u hu hU
  have hle : LinearMap.range a₀ ≤ LinearMap.ker a₁ := by
    rintro _ ⟨y, rfl⟩
    exact LinearMap.congr_fun h10 y
  obtain ⟨d, hdπ⟩ : ∃ d : (P₁ ⧸ LinearMap.range a₀) →ₗ[R] P₂, d ∘ₗ (LinearMap.range a₀).mkQ = a₁ :=
    ⟨_, Submodule.liftQ_mkQ _ _ hle⟩
  obtain ⟨e⟩ := GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_equiv_H1 c0 c1 d hdπ (GlobalTheory.CompanionTheory.PerfectFirstCohomology.qiso_lid (hq' R))
  obtain ⟨hfin, hproj, hrank⟩ := hVB
  have hVBd : MainStatements.Hodge.VB R (LinearMap.ker d) g :=
    ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun p => by
      rw [Module.rankAtStalk_eq_of_equiv e]
      exact hrank p⟩
  have hfibd : ∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (LinearMap.ker (d.baseChange k)) = g := by
    intro k _ _
    obtain ⟨F', m, hg⟩ := hfib k
    obtain ⟨E₀, E₁, E₂, -, -, -, h01, h12⟩ := GlobalTheory.T.cochain_base_change_equivalences R k C F F' m
    obtain ⟨e'⟩ := GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_equiv_base F' E₀ E₁ E₂ h01 h12 c0 c1 d hdπ (hq' k)
    rw [e'.finrank_eq, hg]
  obtain ⟨r', hr'⟩ := GlobalTheory.CompanionTheory.PerfectFirstCohomology.regular_of_fibres R _ P₂ d g hVBd hfibd
  obtain ⟨r, hr⟩ := Module.projective_lifting_property (LinearMap.range a₀).mkQ r' (Submodule.mkQ_surjective _)
  have har : a₁ ∘ₗ r ∘ₗ a₁ = a₁ := by
    rw [← hdπ]
    ext x
    have h₁ := LinearMap.congr_fun hr (d ((LinearMap.range a₀).mkQ x))
    have h₂ := LinearMap.congr_fun hr' ((LinearMap.range a₀).mkQ x)
    simp only [LinearMap.comp_apply] at h₁ h₂ ⊢
    rw [h₁, h₂]
  intro R' _ _ F' m
  obtain ⟨E₀, E₁, E₂, -, hE₁, -, h01, h12⟩ := GlobalTheory.T.cochain_base_change_equivalences R R' C F F' m
  obtain ⟨H₁, H₂⟩ := GlobalTheory.T.quasi_isomorphism_degree_one_kernel R _ _ _ P₀ P₁ P₂
    (GlobalTheory.CatCoh.d0 F) (GlobalTheory.CatCoh.d1 F) a₀ a₁ ψ₀ ψ₁ ψ₂ r
    (GlobalTheory.CatCoh.Z1 F)
    (LinearMap.codRestrict _ (GlobalTheory.CatCoh.d0 F) (GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne F))
    (GlobalTheory.CompanionTheory.PerfectFirstCohomology.mem_Z1_iff_cocycle F) (fun _ => rfl) h10 c0 c1 har hq' R'
  exact GlobalTheory.T.first_cohomology_base_change_of_cochain_equivs R R' C F F' m E₀ E₁ E₂ hE₁ h01 h12 H₁ H₂
end GlobalTheory.CompanionTheory.PerfectFirstCohomology
