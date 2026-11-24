-- Prove2me | solution 1 for GlobalTheory.DegKer.rankAbove_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:23:19.744012+00:00
-- url     : https://prove2.me/submissions/908fa4a7-579d-45ba-9f5d-005ee39a5ced

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel
import Theorems.Thm_GlobalTheory_DegKer_finrank_away

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
theorem _root_.solution {X Y : Scheme.{0}} [IsIntegral Y] (ψ : X ⟶ Y) [IsAffineHom ψ]
    {U : Y.Opens} (hU : IsAffineOpen U) (f : Γ(Y, U)) (hne : (Y.basicOpen f : Set Y).Nonempty) :
    rankAbove ψ (Y.basicOpen f) = rankAbove ψ U := by
  haveI : Nonempty U := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, Y.basicOpen_le f hx⟩⟩
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hne
  letI := (ψ.app U).hom.toAlgebra
  letI := (ψ.app (Y.basicOpen f)).hom.toAlgebra
  let i : ψ ⁻¹ᵁ (Y.basicOpen f) ⟶ ψ ⁻¹ᵁ U := homOfLE (fun x hx => Y.basicOpen_le f hx)
  letI : Algebra Γ(X, ψ ⁻¹ᵁ U) Γ(X, ψ ⁻¹ᵁ (Y.basicOpen f)) := (X.presheaf.map i.op).hom.toAlgebra
  haveI := hU.isLocalization_basicOpen f
  haveI : IsLocalization.Away (algebraMap Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) f) Γ(X, ψ ⁻¹ᵁ (Y.basicOpen f)) :=
    (hU.preimage ψ).isLocalization_of_eq_basicOpen _ i (Scheme.preimage_basicOpen ψ f)
  refine finrank_away (R := Γ(Y, U)) (S := Γ(X, ψ ⁻¹ᵁ U)) (R' := Γ(Y, Y.basicOpen f))
    (S' := Γ(X, ψ ⁻¹ᵁ (Y.basicOpen f))) f hf ?_
  exact congrArg CommRingCat.Hom.hom (ψ.naturality (homOfLE (Y.basicOpen_le f)).op)
end GlobalTheory.DegKer
