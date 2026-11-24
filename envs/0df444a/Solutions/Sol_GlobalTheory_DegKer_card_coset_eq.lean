-- Prove2me | solution 1 for GlobalTheory.DegKer.card_coset_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:05:58.93787+00:00
-- url     : https://prove2.me/submissions/f0bd8fde-809e-4d87-add8-e847c34c13fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
noncomputable section
open GlobalTheory
open GlobalTheory.DegKer
namespace GlobalTheory.DegKer
theorem _root_.solution {S : Scheme.{0}} (A T : Over S) [GrpObj A] (α : A ⟶ A) [IsMonHom α]
    (z : T ⟶ A) (h : Nonempty {y : T ⟶ A // y ≫ α = z}) :
    Nat.card {y : T ⟶ A // y ≫ α = 1} = Nat.card {y : T ⟶ A // y ≫ α = z} := by
  obtain ⟨⟨y₀, rfl⟩⟩ := h
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft y₀) fun y => ?_)
  simp [MonObj.mul_comp]
end GlobalTheory.DegKer
