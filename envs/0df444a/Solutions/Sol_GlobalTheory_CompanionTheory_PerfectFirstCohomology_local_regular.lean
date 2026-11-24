-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomology.local_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:17:13.926939+00:00
-- url     : https://prove2.me/submissions/1d43e4d4-0cd5-45be-8ad2-8673f955b713

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
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_T_linear_map_zero_of_injective_full_rank
import Theorems.Thm_GlobalTheory_T_local_free_kernel_splitting
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
namespace GlobalTheory.CompanionTheory.PerfectFirstCohomology
theorem _root_.solution (A Q P : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [AddCommGroup P]
    [Module A P] [Module.Finite A Q] [Module.Free A Q] [Module.Finite A P] [Module.Free A P] (d : Q →ₗ[A] P) (g : ℕ)
    (h1 : Module.Free A (LinearMap.ker d)) (h2 : Module.Finite A (LinearMap.ker d))
    (h3 : Module.finrank A (LinearMap.ker d) = g)
    (h4 : Module.finrank (IsLocalRing.ResidueField A) (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) = g) :
    ∃ r : P →ₗ[A] Q, d ∘ₗ r ∘ₗ d = d := by
  obtain ⟨r, hidem, hfree, hfin, hrank⟩ := GlobalTheory.T.local_free_kernel_splitting A Q P d
  refine ⟨r, ?_⟩
  have hrank' : Module.finrank A (LinearMap.ker (r ∘ₗ d)) = g := hrank.trans h4
  have hle : LinearMap.ker d ≤ LinearMap.ker (r ∘ₗ d) := fun x hx => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]
  let b := Module.finBasisOfFinrankEq A (LinearMap.ker d) h3
  let φ : (Fin g → A) →ₗ[A] LinearMap.ker (r ∘ₗ d) :=
    Submodule.inclusion hle ∘ₗ b.equivFun.symm.toLinearMap
  have hφ : Function.Injective φ := (Submodule.inclusion_injective hle).comp b.equivFun.symm.injective
  have hzero : (d ∘ₗ (LinearMap.ker (r ∘ₗ d)).subtype) ∘ₗ φ = 0 := LinearMap.ext fun v => by
    change d ((b.equivFun.symm v : LinearMap.ker d) : Q) = 0
    exact LinearMap.mem_ker.mp (b.equivFun.symm v).2
  have key := GlobalTheory.T.linear_map_zero_of_injective_full_rank A _ P g φ
    (d ∘ₗ (LinearMap.ker (r ∘ₗ d)).subtype) hrank' hφ hzero
  ext x
  have hx : x - r (d x) ∈ LinearMap.ker (r ∘ₗ d) := by
    have h := LinearMap.congr_fun hidem x
    simp only [LinearMap.comp_apply] at h
    rw [LinearMap.mem_ker, map_sub, LinearMap.comp_apply, LinearMap.comp_apply, h, sub_self]
  have h := LinearMap.congr_fun key ⟨_, hx⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply, map_sub, sub_eq_zero] at h
  simp only [LinearMap.comp_apply]
  exact h.symm
end GlobalTheory.CompanionTheory.PerfectFirstCohomology
