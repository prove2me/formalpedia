-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfectFirstCohomology.regular_of_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:51.752236+00:00
-- url     : https://prove2.me/submissions/0c320dcd-38ae-4e83-a17f-41cdd25f4874

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
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_local_regular
import Theorems.Thm_GlobalTheory_T_kernel_base_change_tower_equiv
import Theorems.Thm_GlobalTheory_T_kernel_free_at_primes_of_constant_rank
import Theorems.Thm_GlobalTheory_T_local_splitting_kernel_base_change


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
theorem _root_.solution (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P]
    [Module.Finite R Q] [Module.Projective R Q] [Module.Finite R P] [Module.Projective R P] (d : Q →ₗ[R] P) (g : ℕ)
    (hVB : VB R (LinearMap.ker d) g)
    (hfib : ∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (LinearMap.ker (d.baseChange k)) = g) :
    ∃ r : P →ₗ[R] Q, d ∘ₗ r ∘ₗ d = d := by
  obtain ⟨hfin, hproj, hrank⟩ := hVB
  apply GlobalTheory.T.local_splitting_kernel_base_change R Q P d
  intro p hp
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.kernel_free_at_primes_of_constant_rank R Q P d g hfin hproj hrank p
  haveI : Module.Flat (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Q) :=
    Module.Flat.baseChange R _ Q
  haveI : Module.Flat (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] P) :=
    Module.Flat.baseChange R _ P
  haveI : Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Q) :=
    Module.free_of_flat_of_isLocalRing
  haveI : Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] P) :=
    Module.free_of_flat_of_isLocalRing
  refine GlobalTheory.CompanionTheory.PerfectFirstCohomology.local_regular (Localization.AtPrime p) _ _
    (d.baseChange (Localization.AtPrime p)) g h1 h2 h3 ?_
  obtain ⟨e⟩ := GlobalTheory.T.kernel_base_change_tower_equiv R (Localization.AtPrime p)
    (IsLocalRing.ResidueField (Localization.AtPrime p)) Q P d
  rw [e.finrank_eq]
  exact hfib _
end GlobalTheory.CompanionTheory.PerfectFirstCohomology
