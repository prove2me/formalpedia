-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.ust_abelian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:31:27.211887+00:00
-- url     : https://prove2.me/submissions/8348d919-baa6-4038-9971-dbe26d271e3f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteSemilatticeSystemStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSectionsAffineFlatStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AbelianSchemeBaseChangeExistsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUniqueConstantOfCompatibleFamilyStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparisonStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsPullOWOverCompStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatCocycleTensorRepresentationStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleTensorCoboundaryClassZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClassZeroCocycleTensorCoboundaryStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleOnProductFromSecondFactorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyOfBaseZero
import Theorems.Thm_GlobalTheory_T_abelian_scheme_base_change_exists
import Theorems.Thm_GlobalTheory_T_exists_unique_constant_of_compatible_family


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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
namespace GlobalTheory.CompanionTheory.Axis
theorem _root_.solution : DescentSt → LowSt → SysBCSt → SteinSt → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (P : Type) [SemilatticeInf P] (S : Sys A.left P), USt (OSys A.hom S) := by
  intro hD hL hB hS R _ A _ g hA hg P _ S M _ _ z hz
  letI : Module Rᵐᵒᵖ M := Module.compHom M ((RingEquiv.toOpposite R).symm.toRingHom)
  haveI : IsCentralScalar R M := ⟨fun r m ↦ rfl⟩
  obtain ⟨A', _, φ, hA', hg', hpb⟩ := GlobalTheory.T.abelian_scheme_base_change_exists R (TrivSqZeroExt R M) A g hA hg
  have := hA.proper
  have := hA'.proper
  obtain ⟨S', m, -⟩ := hB R (TrivSqZeroExt R M) A.left A'.left A.hom A'.hom φ hpb inferInstance P S
  have hSt : Stein (OSys A'.hom S') :=
    ((hL _ _ _ _ _ (resSys A'.hom S') (hD _ _ A'.hom inferInstance P S')).2.2).1 (hS _ A' g hA' hg')
  exact GlobalTheory.T.exists_unique_constant_of_compatible_family R Pᵒᵖ (OSys A.hom S) M _ m hSt z hz
end GlobalTheory.CompanionTheory.Axis
