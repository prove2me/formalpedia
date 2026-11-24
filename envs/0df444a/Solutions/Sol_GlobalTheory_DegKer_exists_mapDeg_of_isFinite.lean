-- Prove2me | solution 1 for GlobalTheory.DegKer.exists_mapDeg_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:31:55.837723+00:00
-- url     : https://prove2.me/submissions/fb913c4d-a3c6-4188-b6b0-da8253cfd318

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel
import Theorems.Thm_GlobalTheory_DegKer_rankAbove_basicOpen
import Theorems.Thm_GlobalTheory_ZV_MapDeg_of_isFinite


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
theorem _root_.solution : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (ψ : X ⟶ Y), IsFinite ψ → Surjective ψ → ∃ D : ℕ, 1 ≤ D ∧ MapDeg ψ D := by
  intro X Y _ _ ψ hfin hsurj
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  refine ⟨rankAbove ψ U, ?_, MapDeg.of_isFinite fun V hV hne => ?_⟩
  · obtain ⟨x, rfl⟩ := ψ.surjective y
    haveI : Nonempty U := ⟨⟨_, hyU⟩⟩
    haveI : Nonempty (ψ ⁻¹ᵁ U) := ⟨⟨x, hyU⟩⟩
    letI := (ψ.app U).hom.toAlgebra
    haveI : Module.Finite Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) := ψ.finite_app U hU
    haveI := IsSchemeTheoreticallyDominant.of_isDominant ψ
    haveI : FaithfulSMul Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (ψ.app_injective U)
    exact Module.finrank_pos
  · obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen ⟨y, hyU⟩ hne
    obtain ⟨f, g, e, hzf⟩ := exists_basicOpen_le_affine_inter hU hV z hz
    change rankAbove ψ V = rankAbove ψ U
    rw [← rankAbove_basicOpen ψ hU f ⟨z, hzf⟩, ← rankAbove_basicOpen ψ hV g ⟨z, e ▸ hzf⟩, e]
end GlobalTheory.DegKer
