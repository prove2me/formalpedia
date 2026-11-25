-- Prove2me | solution 1 for GlobalTheory.FiniteCover.chart_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:25:36.093864+00:00
-- url     : https://prove2.me/submissions/6d3549f9-949d-45fa-87e3-7b7ab2c3e495

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCommonMultiple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FinrankSecPullSandwich
import Theorems.Thm_GlobalTheory_FiniteCover_rankAtStalk_bot
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_FiniteCover_exists_denominator
import Theorems.Thm_GlobalTheory_FiniteCover_toField_appLE
import Theorems.Thm_GlobalTheory_FiniteCover_toField_injective
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.FiniteCover
variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
namespace GlobalTheory.FiniteCover
theorem _root_.solution (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ]
    [Algebra X.functionField X'.functionField]
    (hF : ∀ x, algebraMap X.functionField X'.functionField x = functionFieldMap φ x)
    {D : X.Opens} (hD : IsAffineOpen D) (h : genericPoint X ∈ D) :
    (∃ x, Module.finrank X.functionField X'.functionField = φ.finrank x) ∧
    ∀ {d : ℕ} (e : Module.Basis (Fin d) X.functionField X'.functionField),
      ∃ c ∈ (toField h).range, c ≠ 0 ∧
        (∀ j, ∀ y ∈ (toField (generic_mem_preimage φ h)).range, c * e.repr y j ∈ (toField h).range) ∧
        ∀ j, c • e j ∈ (toField (generic_mem_preimage φ h)).range := by
  have h' := generic_mem_preimage φ h
  haveI : Nonempty D := ⟨⟨_, h⟩⟩
  haveI : Nonempty (φ ⁻¹ᵁ D) := ⟨⟨_, h'⟩⟩
  letI := (φ.app D).hom.toAlgebra
  haveI : Module.Finite Γ(X, D) Γ(X', φ ⁻¹ᵁ D) := φ.finite_app D hD
  haveI : Module.Flat Γ(X, D) Γ(X', φ ⁻¹ᵁ D) := by
    have := φ.flat_appLE hD (hD.preimage φ) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  haveI := functionField_isFractionRing_of_isAffineOpen X D hD
  haveI := functionField_isFractionRing_of_isAffineOpen X' _ (hD.preimage φ)
  letI : Algebra Γ(X, D) X'.functionField :=
    ((algebraMap X.functionField X'.functionField).comp (algebraMap Γ(X, D) X.functionField)).toAlgebra
  haveI : IsScalarTower Γ(X, D) X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower Γ(X, D) Γ(X', φ ⁻¹ᵁ D) X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => by
      have e := toField_appLE φ le_rfl h h' a
      rw [Scheme.Hom.appLE_eq_app] at e
      exact (hF _).trans e.symm
  refine ⟨⟨hD.fromSpec (⊥ : PrimeSpectrum Γ(X, D)), ?_⟩, fun e => ?_⟩
  · have hp : IsPullback (hD.preimage φ).fromSpec (Spec.map (φ.app D)) φ hD.fromSpec :=
      (IsOpenImmersion.isPullback _ _ _ _ (by
        rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hD (hD.preimage φ)])
        (by simp)).flip
    rw [IsFractionRing.finrank_eq Γ(X, D) X.functionField Γ(X', φ ⁻¹ᵁ D) X'.functionField,
      ← rankAtStalk_bot]
    refine Eq.trans ?_ (Scheme.Hom.finrank_of_isPullback _ _ _ _ hp _)
    exact (Scheme.Hom.finrank_SpecMap_algebraMap Γ(X, D) Γ(X', φ ⁻¹ᵁ D) _).symm
  · obtain ⟨c, hc, h₁, h₂⟩ := exists_denominator (A := Γ(X, D)) (C := Γ(X', φ ⁻¹ᵁ D)) e
    refine ⟨toField h c, ⟨c, rfl⟩, fun h0 => hc (toField_injective h (h0.trans (map_zero _).symm)),
      ?_, h₂⟩
    rintro j _ ⟨y, rfl⟩
    exact h₁ j y
end GlobalTheory.FiniteCover
