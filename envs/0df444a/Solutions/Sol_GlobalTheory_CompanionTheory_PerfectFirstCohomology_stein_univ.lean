-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomology.stein_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:01.310794+00:00
-- url     : https://prove2.me/submissions/7b114d55-1710-420d-a2fe-d4b1754c26aa

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
import Theorems.Thm_GlobalTheory_T_cochain_base_change_equivalences
import Theorems.Thm_GlobalTheory_T_retract_base_change_kernel_compatible
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
theorem _root_.solution (R C : Type) [CommRing R] [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')]
    (F : C ⥤ CommAlgCat.{0} R) (hS : SteinU F) (M : Type) [AddCommGroup M] [Module R M] :
    Function.Injective (fun m : M ↦ m ⊗ₜ[R] (1 : C0 F)) ∧
      ∀ x : M ⊗[R] C0 F, (d0 F).lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] (1 : C0 F) = x := by
  letI : Module Rᵐᵒᵖ M := Module.compHom M ((RingHom.id R).fromOpposite fun x y => Commute.all _ _)
  haveI : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  haveI : IsScalarTower R Rᵐᵒᵖ M := ⟨fun r s m => mul_smul r (MulOpposite.unop s) m⟩
  haveI : SMulCommClass R Rᵐᵒᵖ M := ⟨fun r s m => smul_comm r (MulOpposite.unop s) m⟩
  obtain ⟨F', m, hF'⟩ := hS (TrivSqZeroExt R M)
  obtain ⟨E₀, E₁, E₂, h0, -, -, h01, -⟩ :=
    GlobalTheory.T.cochain_base_change_equivalences R (TrivSqZeroExt R M) C F F' m
  have hone : E₀ (1 ⊗ₜ[R] (1 : GlobalTheory.CatCoh.C0 F)) = 1 := by
    rw [h0]
    funext T
    first
      | exact map_one _
      | simp
  refine GlobalTheory.T.retract_base_change_kernel_compatible R (TrivSqZeroExt R M) M _ _ _ _
    (TrivSqZeroExt.inrHom R M) (TrivSqZeroExt.sndHom R M) (GlobalTheory.CatCoh.d0 F)
    (GlobalTheory.CatCoh.d0 F') E₀ E₁ 1 (LinearMap.ext fun _ => rfl) h01 ?_ ?_
  · intro r hr
    rw [hone, ← Algebra.algebraMap_eq_smul_one] at hr
    exact hF'.2 (hr.trans (map_zero _).symm)
  · intro z hz
    obtain ⟨r, hr⟩ := (hF'.1 z).mp hz
    exact ⟨r, by rw [hone, ← Algebra.algebraMap_eq_smul_one, ← Algebra.linearMap_apply]; exact hr⟩
end GlobalTheory.CompanionTheory.PerfectFirstCohomology
