-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:15.270899+00:00
-- url     : https://prove2.me/submissions/9fb42694-efa3-45bb-af3f-cd22b5ce591f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_BoxMulA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GlobalUnitScalingHaarProductFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ProdFormula_map_mul_left_infinite
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ProdFormula_norm_algebraMap_infinite
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ProdFormula_map_mul_left_finite
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_finiteSingleUnits
import Theorems.Thm_GroundTheory_Global_finiteAdeleEval_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_finiteSingleUnits
attribute [local simp] GroundTheory.Global.finiteAdeleEval_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ProdFormula
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW.ProdFormula
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (a : F), a ≠ 0 →
    ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧
      (∀ μ : Measure (Ainf F), μ.IsAddHaarMeasure →
        μ.map (fun x => algebraMap F (Ainf F) a * x) = cinf • μ) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure →
        μ.map (fun x => algebraMap F (Fv F v) a * x) = c v • μ := by
  intro F _ _ a ha
  have hA : 0 < ∏ w : InfinitePlace F, w a ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 ha) _
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖algebraMap F (Fv F v) a‖).Finite :=
    (FinitePlace.hasFiniteMulSupport ha).preimage
      (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
  have hprod : (∏ w : InfinitePlace F, w a ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖ = 1 := by
    rw [← prod_abs_eq_one ha, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    rfl
  refine ⟨((∏ w : InfinitePlace F, w a ^ w.mult)⁻¹).toNNReal,
    fun v => (‖algebraMap F (Fv F v) a‖₊)⁻¹, ⟨?_, ?_⟩, ?_, ?_⟩
  · filter_upwards [hfin.eventually_cofinite_notMem] with v hv
    have h1 : ‖algebraMap F (Fv F v) a‖ = 1 := by simpa using hv
    have h2 : ‖algebraMap F (Fv F v) a‖₊ = 1 := NNReal.coe_injective h1
    rw [h2, inv_one]
  · apply NNReal.coe_injective
    have e : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (‖algebraMap F (Fv F v) a‖₊)⁻¹ : ℝ≥0) : ℝ) =
        (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖)⁻¹ := by
      rw [finprod_inv_distrib]
      rw [NNReal.coe_inv]
      congr 1
      exact NNReal.toRealHom.map_finprod_of_injective NNReal.coe_injective _
    rw [NNReal.coe_mul, e, NNReal.coe_one, Real.coe_toNNReal _ (inv_pos.2 hA).le, ← mul_inv, hprod, inv_one]
  · intro μ hμ
    have hb : (((Units.map (algebraMap F (Ainf F)).toMonoidHom (Units.mk0 a ha))⁻¹ : (Ainf F)ˣ) : Ainf F) =
        algebraMap F (Ainf F) a⁻¹ := by
      simp
    have h := map_mul_left_infinite (F := F) (m := measAinf) ⟨rfl⟩
      (Units.map (algebraMap F (Ainf F)).toMonoidHom (Units.mk0 a ha)) μ hμ
    rw [hb, norm_algebraMap_infinite] at h
    have e : ∏ w : InfinitePlace F, w a⁻¹ ^ w.mult = (∏ w : InfinitePlace F, w a ^ w.mult)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [map_inv₀, inv_pow]
    rw [e] at h
    exact h
  · intro v μ hμ
    exact map_mul_left_finite v _ ((map_ne_zero _).2 ha) μ hμ
end GlobalTheory.CompanionTheory.SW.ProdFormula
