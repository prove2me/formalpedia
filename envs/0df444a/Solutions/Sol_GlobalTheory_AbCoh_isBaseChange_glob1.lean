-- Prove2me | solution 1 for GlobalTheory.AbCoh.isBaseChange_glob1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:10:49.494352+00:00
-- url     : https://prove2.me/submissions/f336516e-3c23-483b-8929-63a29cca9660

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalOneFormFrameCoordinatesConstantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsBaseChangeCompatibleGlobalOneForms
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
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
theorem _root_.solution (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hF : HasFrame F) (h0 : CohomZeroIsConstants F) (T : C) (e : Glob1 F →ₗ[R] Ω[F.obj T⁄R]) (he : ∀ w, e w = w.1 T) :
    IsBaseChange (F.obj T) e := by
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨l, hl, hsum⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ
  let S := F.obj T
  let fwd : S ⊗[R] Glob1 F →ₗ[S] Ω[F.obj T⁄R] := e.liftBaseChange S
  let inv : Ω[F.obj T⁄R] →ₗ[S] S ⊗[R] Glob1 F :=
    ∑ i, (Φ.δ i T).smulRight ((1 : S) ⊗ₜ[R] Φ.w i)
  have hinv : ∀ ω, inv ω = ∑ i, Φ.δ i T ω ⊗ₜ[R] Φ.w i := by
    intro ω
    simp only [inv, LinearMap.sum_apply, LinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have h1 : ∀ ω, fwd (inv ω) = ω := by
    intro ω
    rw [hinv, map_sum]
    simp only [fwd, LinearMap.liftBaseChange_tmul, he]
    exact (Φ.sum T ω).symm
  have h2 : ∀ x, inv (fwd x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul b w =>
      have : ∑ i, Φ.δ i T (w.1 T) ⊗ₜ[R] Φ.w i = (1 : S) ⊗ₜ[R] w := by
        conv_rhs => rw [hsum w]
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hl, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      show inv (e.liftBaseChange S (b ⊗ₜ[R] w)) = _
      rw [LinearMap.liftBaseChange_tmul, map_smul, he, hinv, this, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  exact IsBaseChange.of_equiv (LinearEquiv.ofLinear fwd inv (LinearMap.ext h1) (LinearMap.ext h2))
    (fun w ↦ by simp [fwd])
end GlobalTheory.AbCoh
