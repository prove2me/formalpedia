-- Prove2me | solution 1 for GlobalTheory.AbCoh.exists_vf_of_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:19:44.498804+00:00
-- url     : https://prove2.me/submissions/ac50d268-64d2-4069-a18d-a6bad24227a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomologyDerivativeRelationPairingWellDefined
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
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
theorem _root_.solution {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hF : HasFrame F) (h0 : CohomZeroIsConstants F) (l : Glob1 F →ₗ[R] R) :
    ∃ δ : ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T,
      (∀ ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ T' (p1 F φ ω) = mp F φ (δ T ω)) ∧
      ∀ (w : Glob1 F) T, δ T (w.1 T) = algebraMap R (F.obj T) (l w) := by
  obtain ⟨m, ⟨fr⟩⟩ := hF
  refine ⟨fun T ↦ ∑ i, algebraMap R (F.obj T) (l (fr.w i)) • fr.δ i T, fun T T' φ ω ↦ ?_, fun w T ↦ ?_⟩
  · simp only [LinearMap.sum_apply, LinearMap.smul_apply, fr.nat, smul_eq_mul, map_sum,
      map_mul, AlgHom.commutes]
  · have hc : ∀ i, ∃ c : R, ∀ T, fr.δ i T (w.1 T) = algebraMap R (F.obj T) c := fun i ↦ by
      obtain ⟨c, hc, -⟩ := h0 (fun T ↦ fr.δ i T (w.1 T)) (by
        funext T T' φ
        simp only [amitsur_d0_apply, Pi.zero_apply]
        rw [w.2 φ, fr.nat, sub_self])
      exact ⟨c, hc⟩
    choose c hc using hc
    have hw : w = ∑ i, c i • fr.w i := by
      refine Subtype.ext (funext fun T ↦ ?_)
      rw [fr.sum T (w.1 T)]
      simp only [hc, algebraMap_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    conv_rhs => rw [hw]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smul, hc, smul_eq_mul,
      map_mul]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
end GlobalTheory.AbCoh
