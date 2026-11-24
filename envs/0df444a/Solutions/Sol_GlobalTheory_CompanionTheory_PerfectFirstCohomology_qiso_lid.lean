-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomology.qiso_lid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:17:14.260268+00:00
-- url     : https://prove2.me/submissions/92b08266-0076-492a-a5ee-850dda046be9

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
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_lid_natural

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
theorem _root_.solution {R A₀ A₁ A₂ B₀ B₁ B₂ : Type} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    (h : QIsoAt (a₀.lTensor R) (a₁.lTensor R) (b₀.lTensor R) (b₁.lTensor R) (f.lTensor R)) :
    QIsoAt a₀ a₁ b₀ b₁ f :=
  qiso_transport h (TensorProduct.lid R A₀).toAddEquiv (TensorProduct.lid R A₁).toAddEquiv
    (TensorProduct.lid R A₂).toAddEquiv (TensorProduct.lid R B₀).toAddEquiv
    (TensorProduct.lid R B₁).toAddEquiv (TensorProduct.lid R B₂).toAddEquiv
    (lid_natural a₀) (lid_natural a₁) (lid_natural b₀) (lid_natural b₁) (lid_natural f)
end GlobalTheory.CompanionTheory.PerfectFirstCohomology
