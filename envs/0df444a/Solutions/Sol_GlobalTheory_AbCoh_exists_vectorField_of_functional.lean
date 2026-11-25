-- Prove2me | solution 1 for GlobalTheory.AbCoh.exists_vectorField_of_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:10:45.359396+00:00
-- url     : https://prove2.me/submissions/a7892e93-e746-4084-8dd5-7392e89f8660

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalOneFormFrameCoordinatesConstantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalVectorFieldOfOneFormFunctional
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_T_globalOneFormFrame_coordinates_constant
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ l : Glob1 F →ₗ[R] R, ∃ δ : ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T, (∀ ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ T' (p1 F φ ω) = mp F φ (δ T ω)) ∧ ∀ (w : Glob1 F) T, δ T (w.1 T) = algebraMap R (F.obj T) (l w) := by
  intro R _ C _ F hF h0 l
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨c, hc, hsum⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ
  refine ⟨fun T ↦ ∑ i, algebraMap R (F.obj T) (l (Φ.w i)) • Φ.δ i T, ?_, ?_⟩
  · intro T T' φ ω
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul,
      AlgHom.commutes, Φ.nat]
  · intro w T
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hc, ← map_mul, ← map_sum]
    have hw : l w = l (∑ i, c i w • Φ.w i) := congrArg l (hsum w)
    rw [hw, map_sum]
    simp [mul_comm]
end GlobalTheory.AbCoh
