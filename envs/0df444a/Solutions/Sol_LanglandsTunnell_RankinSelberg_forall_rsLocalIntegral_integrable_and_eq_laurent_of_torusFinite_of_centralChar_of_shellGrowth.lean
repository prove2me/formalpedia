-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_rsLocalIntegral_integrable_and_eq_laurent_of_torusFinite_of_centralChar_of_shellGrowth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/119c57db-bd2b-54c9-a5e8-4aebebbed793

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_HaarQuotient_exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_integrable_rsLocalIntegrand_of_gauge
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_dual_rsLocalIntegrand_of_gauge
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_iotaGL_eq_of_forall_torusShell_localLevelOne_pow_eq_zero
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_rsLocalIntegral_dualWhittakerFn3_iotaGL_eq_of_forall_torusShell_transposeInvN_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_integrable_and_eq_laurent_of_torusFinite_of_centralChar_of_shellGrowth
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal"
p2m_attr_erase "simp" "Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
open scoped ENNReal NNReal Matrix

noncomputable section

namespace RSParentGrowth

section Basic

open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def qR : ℝ := ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ)

theorem one_lt_qR : 1 < qR v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [qR]; exact_mod_cast this

theorem qR_pos : 0 < qR v := zero_lt_one.trans (one_lt_qR v)

theorem qR_eq_natCast : qR v = (Ideal.absNorm v.asIdeal : ℝ) := NNReal.coe_natCast _

theorem norm_eq_zpow_of_v_eq_exp (x : F) (m : ℤ) (hx : Valued.v x = WithZero.exp m) : ‖x‖ = qR v ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    NNReal.coe_zpow, qR]
  congr 1

theorem coe_modulus_eq_norm (x : F) : ((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

theorem exists_modulus_det_eq_zpow (h : G) : ∃ m : ℤ,
    ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F) : ℝ≥0) : ℝ) = qR v ^ m := by
  have hne : Valued.v ((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  refine ⟨WithZero.log (Valued.v ((Matrix.GeneralLinearGroup.det h : (F)ˣ) : F)), ?_⟩
  rw [coe_modulus_eq_norm]
  exact norm_eq_zpow_of_v_eq_exp v _ _ (WithZero.exp_log hne).symm

abbrev unip : Subgroup G := (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ v)).range

theorem coe_unip_eq :
    ((unip v : Subgroup G) : Set G) = {g : G | (g : Mat) 0 0 = 1 ∧ (g : Mat) 1 0 = 0 ∧ (g : Mat) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [unipotentGL2Hom, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Mat) 0 1), Units.ext ?_⟩
    change ((unipotentGL2 ((g : Mat) 0 1) : G) : Mat) = (g : Mat)
    rw [unipotentGL2_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_unip : IsClosed ((unip v : Subgroup G) : Set G) := by
  rw [coe_unip_eq]
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := fun i j =>
    (Units.continuous_val).matrix_elem i j
  exact ((isClosed_singleton.preimage (hc 0 0)).inter
    ((isClosed_singleton.preimage (hc 1 0)).inter (isClosed_singleton.preimage (hc 1 1))))

theorem unip_comm (a b : (unip v : Subgroup G)) : a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  refine Subtype.ext ?_
  change (a : G) * b = b * a
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem unipotent_eq_unipotentGL2 (x : F) : UnramifiedWhittaker.unipotent x = (unipotentGL2 x : G) := by
  refine Units.ext ?_
  rw [unipotentGL2_coe]
  simp [UnramifiedWhittaker.unipotent]

theorem det_unipotentGL2 (x : F) : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion ℚ v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem continuous_iotaGL : Continuous fun g : G => (iotaGL g : G₃) := by
  rw [Units.continuous_iff]
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := fun i j =>
    (Units.continuous_val).matrix_elem i j
  have hci : ∀ i j : Fin 2, Continuous fun g : G => ((g⁻¹ : G) : Mat) i j := fun i j =>
    (Units.continuous_coe_inv).matrix_elem i j
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [Function.comp_apply, coe_iotaGL, embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact hc _ _
  · have h : ∀ g : G, ((((iotaGL g : G₃)⁻¹ : G₃)) : Matrix (Fin 3) (Fin 3) F) = embedMat2 ((g⁻¹ : G) : Mat) :=
      fun g => by rw [← map_inv, coe_iotaGL]
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact hci _ _

theorem continuous_transposeInvN : Continuous fun g : G => transposeInvN (Fin 2) g := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun g : G => (((g⁻¹ : G)) : Mat)ᵀ
    exact (Units.continuous_coe_inv (M := Mat)).matrix_transpose
  · change Continuous fun g : G => ((g : G) : Mat)ᵀ
    exact (Units.continuous_val (M := Mat)).matrix_transpose

theorem continuous_transposeInv3 : Continuous fun g : G₃ => transposeInv3 g := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun g : G₃ => (((g⁻¹ : G₃)) : Matrix (Fin 3) (Fin 3) F)ᵀ
    exact (Units.continuous_coe_inv (M := Matrix (Fin 3) (Fin 3) F)).matrix_transpose
  · change Continuous fun g : G₃ => ((g : G₃) : Matrix (Fin 3) (Fin 3) F)ᵀ
    exact (Units.continuous_val (M := Matrix (Fin 3) (Fin 3) F)).matrix_transpose

theorem continuous_of_rightInvariant {H : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
    {α : Type*} [TopologicalSpace α]
    {f : H → α} {U : Subgroup H} (hU : IsOpen (U : Set H)) (hf : ∀ k ∈ U, ∀ g : H, f (g * k) = f g) :
    Continuous f := by
  refine (IsLocallyConstant.iff_exists_open f).mpr (fun x => ?_) |>.continuous
  refine ⟨(fun h => x⁻¹ * h) ⁻¹' (U : Set H), hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro y hy
    have := hf (x⁻¹ * y) hy x
    rwa [mul_inv_cancel_left] at this

section UnitsMeasure

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

theorem borelSpace_loc : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v

attribute [local instance] borelSpace_loc

theorem borelSpace_locUnits : BorelSpace (v.adicCompletion ℚ)ˣ := by
  refine ⟨?_⟩
  have h : (inferInstance : TopologicalSpace (v.adicCompletion ℚ)ˣ) =
      TopologicalSpace.induced (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) inferInstance :=
    Units.isEmbedding_val₀.eq_induced
  show MeasurableSpace.comap Units.val (borel (v.adicCompletion ℚ)) = borel (v.adicCompletion ℚ)ˣ
  exact ((congrArg (fun t => @borel (v.adicCompletion ℚ)ˣ t) h).trans borel_comap).symm

attribute [local instance] borelSpace_locUnits

theorem isAddHaarMeasure_selfDualHaarAt : (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    have h : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-(LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-(LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2))
    • Measure.addHaarMeasure (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v) :
      Measure (v.adicCompletion ℚ))).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

attribute [local instance] isAddHaarMeasure_selfDualHaarAt

theorem isHaarMeasure_locMul :
    (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) :
      Measure (v.adicCompletion ℚ)ˣ).IsHaarMeasure :=
  LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ v (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)

end UnitsMeasure

end Basic

section Cyclic

open LanglandsTunnell.CubicInduction

variable {A : Type*} [CommRing A]

theorem law_of_mem_gl3CyclicSubspace {ψ : AddChar A ℂ} {W₀ W : GL (Fin 3) A → ℂ} (h₀ : IsGL3PsiWhittakerFn ψ W₀)
    (hW : W ∈ gl3CyclicSubspace W₀) : IsGL3PsiWhittakerFn ψ W := by
  have hmem : W₀ ∈ gl3PsiWhittakerFnSpace A ℂ ψ := (mem_gl3PsiWhittakerFnSpace_iff ψ W₀).mpr h₀
  have hle : gl3CyclicSubspace W₀ ≤ gl3PsiWhittakerFnSpace A ℂ ψ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace ψ h hmem
  exact (mem_gl3PsiWhittakerFnSpace_iff ψ W).mp (hle hW)

theorem smooth_of_mem_span_translates {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {w₀ w : H → ℂ}
    (hsm : ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ k ∈ U, ∀ g, w₀ (g * k) = w₀ g)
    (hw : w ∈ Submodule.span ℂ (Set.range fun h : H => fun g : H => w₀ (g * h))) :
    ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ k ∈ U, ∀ g, w (g * k) = w g := by
  obtain ⟨U₀, hU₀, hfix⟩ := hsm
  refine Submodule.span_induction (p := fun (w : H → ℂ) _ =>
      ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ k ∈ U, ∀ g, w (g * k) = w g) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨h, rfl⟩
    refine ⟨U₀.map (MulAut.conj h).toMonoidHom, ?_, ?_⟩
    · have : ((U₀.map (MulAut.conj h).toMonoidHom : Subgroup H) : Set H) =
          (Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹) '' (U₀ : Set H) := by
        ext x
        simp only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Set.mem_image, SetLike.mem_coe,
          Homeomorph.trans_apply, Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight]
      rw [this]
      exact (Homeomorph.isOpenMap _) _ hU₀
    · rintro k ⟨u, hu, rfl⟩ g
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have : g * (h * u * h⁻¹) * h = g * h * u := by group
      rw [this, hfix u hu]
  · exact ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩
  · rintro w₁ w₂ _ _ ⟨U₁, hU₁, h₁⟩ ⟨U₂, hU₂, h₂⟩
    refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk g => ?_⟩
    simp only [Pi.add_apply, h₁ k hk.1 g, h₂ k hk.2 g]
  · rintro c w _ ⟨U, hU, h⟩
    exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply, h k hk g]⟩

theorem smooth_of_mem_gl3CyclicSubspace [TopologicalSpace A] [IsTopologicalRing A] {W₀ W : GL (Fin 3) A → ℂ}
    (hsm : ∃ U : Subgroup (GL (Fin 3) A), IsOpen (U : Set (GL (Fin 3) A)) ∧ ∀ k ∈ U, ∀ g, W₀ (g * k) = W₀ g)
    (hW : W ∈ gl3CyclicSubspace W₀) :
    ∃ U : Subgroup (GL (Fin 3) A), IsOpen (U : Set (GL (Fin 3) A)) ∧ ∀ k ∈ U, ∀ g, W (g * k) = W g :=
  smooth_of_mem_span_translates hsm hW

variable {F₀ : Type*} [Field F₀]

theorem law_of_mem_span_range (ψ : AddChar F₀ ℂ) (w₀ : GL (Fin 2) F₀ → ℂ)
    (hlaw : ∀ (x : F₀) (g : GL (Fin 2) F₀), w₀ (unipotent x * g) = ψ x * w₀ g)
    {W : GL (Fin 2) F₀ → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) F₀ => fun g : GL (Fin 2) F₀ => w₀ (g * h))) :
    ∀ (x : F₀) (g : GL (Fin 2) F₀), W (unipotent x * g) = ψ x * W g := by
  refine Submodule.span_induction (p := fun W _ => ∀ (x : F₀) (g : GL (Fin 2) F₀),
      W (unipotent x * g) = ψ x * W g) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩ x g
    simp only [mul_assoc, hlaw]
  · intro x g
    simp
  · intro W₁ W₂ _ _ h₁ h₂ x g
    simp only [Pi.add_apply, h₁ x g, h₂ x g, mul_add]
  · intro c W _ hW' x g
    simp only [Pi.smul_apply, hW' x g, smul_eq_mul]
    ring

end Cyclic

section Integrands

open LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def modC (g : G) : ℂ :=
  ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ)

def modR (g : G) : ℝ :=
  ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      HeightOneSpectrum.adicCompletion ℚ v) : ℝ))

theorem modC_eq (g : G) : modC g = ((modR g : ℝ) : ℂ) := rfl

theorem modR_nonneg (g : G) : 0 ≤ modR g := NNReal.coe_nonneg _

theorem modR_mul (g h : G) : modR (g * h) = modR g * modR h := by
  unfold modR
  rw [map_mul, Units.val_mul, LanglandsTunnell.TateLocal.modulus_mul, NNReal.coe_mul]

theorem modC_mul (g h : G) : modC (g * h) = modC g * modC h := by
  rw [modC_eq, modC_eq, modC_eq, modR_mul, Complex.ofReal_mul]

theorem modR_pos (g : G) : 0 < modR g := by
  unfold modR
  exact_mod_cast LanglandsTunnell.TateLocal.modulus_pos (K := F) (Units.ne_zero _)

theorem modC_ne_zero (g : G) : modC g ≠ 0 := by
  rw [modC_eq]
  exact_mod_cast (modR_pos g).ne'

theorem modC_cpow_mul (g h : G) (r : ℂ) : modC (g * h) ^ r = modC g ^ r * modC h ^ r := by
  rw [modC_mul, modC_eq, modC_eq, Complex.mul_cpow_ofReal_nonneg (modR_nonneg g) (modR_nonneg h)]

def phiP (W : LocalGL3 v → ℂ) (w : G → ℂ) (s : ℂ) (g : G) : ℂ := (W (iotaGL g) * w g) * modC g ^ (s - 1 / 2)

def phiD (W : LocalGL3 v → ℂ) (w : G → ℂ) (w₀p : G) (s : ℂ) (g : G) : ℂ :=
  (dualWhittakerFn3 W (iotaGL g) * (modC g * w (w₀p * transposeInvN (Fin 2) g))) * modC g ^ (s - 1 / 2)

theorem continuous_modC : Continuous (modC (v := v)) := by
  have : (modC (v := v)) = fun g : G => ((‖(g : Mat).det‖ : ℝ) : ℂ) := by
    funext g
    rw [modC, coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))

theorem eq_gl2Weyl_of_coe {w₀p : G} (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) : w₀p = gl2Weyl :=
  Units.ext (hw₀p.trans (gl2Weyl_val).symm)

theorem phiP_unipotent_mul {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    {w : G → ℂ} (hw : ∀ (x : F) (g : G), w (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * w g)
    (s : ℂ) : ∀ (x : ↥(unip v)) (g : G), phiP W w s ((x : G) * g) = phiP W w s g := by
  rintro ⟨_, ⟨z, rfl⟩⟩ g
  have hx : (unipotentGL2Hom z : G) = unipotentGL2 z.toAdd := rfl
  show phiP W w s (unipotentGL2Hom z * g) = phiP W w s g
  unfold phiP modC
  rw [hx, map_mul, iotaGL_unipotentGL2, hW, map_mul, det_unipotentGL2, one_mul, ← unipotent_eq_unipotentGL2, hw,
    AddChar.inv_apply, add_zero]
  congr 1
  calc (NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * W (iotaGL g) *
        ((NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd * w g)
      = ((NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * (NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd) *
          (W (iotaGL g) * w g) := by ring
    _ = W (iotaGL g) * w g := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

theorem coe_transposeInv3_upperUnipotent3 (x y z : F) :
    ((transposeInv3 (upperUnipotent3 x y z) : G₃) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; -x, 1, 0; x * y - z, -y, 1] := by
  have hinv : (((upperUnipotent3 x y z)⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F) = !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl
  change (((upperUnipotent3 x y z)⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F)ᵀ = _
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

theorem transposeInv3_mul (g h : G₃) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change (((g * h)⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F)ᵀ =
    (((g⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F))ᵀ * (((h⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F))ᵀ
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : G₃) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((g : G₃) : Matrix (Fin 3) (Fin 3) F))ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _

theorem longWeyl3_mul_self : (longWeyl3 : G₃) * longWeyl3 = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem isGL3PsiWhittakerFn_dualWhittakerFn3 {ψ : AddChar F ℂ} {W : G₃ → ℂ} (hW : IsGL3PsiWhittakerFn ψ⁻¹ W) :
    IsGL3PsiWhittakerFn ψ (dualWhittakerFn3 W) := by
  intro x y z g
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul]
  have hconj : (longWeyl3 : G₃) * transposeInv3 (upperUnipotent3 x y z) * longWeyl3 = upperUnipotent3 (-y) (-x) (x * y - z) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_transposeInv3_upperUnipotent3, longWeyl3_coe, upperUnipotent3_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have h : (longWeyl3 : G₃) * (transposeInv3 (upperUnipotent3 x y z) * transposeInv3 g) =
      upperUnipotent3 (-y) (-x) (x * y - z) * (longWeyl3 * transposeInv3 g) := by
    rw [← hconj]
    have : (longWeyl3 : G₃) * (transposeInv3 (upperUnipotent3 x y z) * transposeInv3 g) =
        longWeyl3 * transposeInv3 (upperUnipotent3 x y z) * longWeyl3⁻¹ * (longWeyl3 * transposeInv3 g) := by group
    rw [this, inv_eq_of_mul_eq_one_right (longWeyl3_mul_self (v := v))]
  rw [h, hW, AddChar.inv_apply]
  congr 2
  ring

theorem dualWhittakerFn3_iotaGL_unipotent_mul {W : LocalGL3 v → ℂ}
    (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W) (x : F) (X : G₃) :
    dualWhittakerFn3 W (iotaGL (unipotentGL2 x : G) * X) =
      NumberField.StandardAddChar.psiLocal ℚ v x * dualWhittakerFn3 W X := by
  have hWd : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v) (dualWhittakerFn3 W) :=
    isGL3PsiWhittakerFn_dualWhittakerFn3 hW
  rw [iotaGL_unipotentGL2, hWd, add_zero]

theorem phiD_unipotent_mul {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    {w : G → ℂ} (hw : ∀ (x : F) (g : G), w (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * w g)
    {w₀p : G} (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (s : ℂ) :
    ∀ (x : ↥(unip v)) (g : G), phiD W w w₀p s ((x : G) * g) = phiD W w w₀p s g := by
  rintro ⟨_, ⟨z, rfl⟩⟩ g
  have hx : (unipotentGL2Hom z : G) = unipotentGL2 z.toAdd := rfl
  show phiD W w w₀p s (unipotentGL2Hom z * g) = phiD W w w₀p s g

  have hconj : w₀p * transposeInvN (Fin 2) (unipotentGL2 z.toAdd * g) =
      UnramifiedWhittaker.unipotent (-z.toAdd) * (w₀p * transposeInvN (Fin 2) g) := by
    rw [transposeInvN_mul, ← mul_assoc, ← mul_assoc]
    congr 1
    refine Units.ext ?_
    have hinv : (((unipotentGL2 z.toAdd : G)⁻¹ : G) : Mat) = !![1, -z.toAdd; 0, 1] := by
      rw [← hx, ← map_inv]; rfl
    rw [Units.val_mul, Units.val_mul, coe_transposeInvN, hinv, hw₀p]
    simp only [UnramifiedWhittaker.unipotent, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  unfold phiD modC
  rw [hx, map_mul, dualWhittakerFn3_iotaGL_unipotent_mul hW, map_mul, det_unipotentGL2, one_mul, hconj, hw]
  congr 1
  calc (NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd * dualWhittakerFn3 W (iotaGL g) *
        (((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
          HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ) *
          ((NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * w (w₀p * transposeInvN (Fin 2) g)))
      = ((NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * (NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd) *
          (dualWhittakerFn3 W (iotaGL g) *
            (((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
              HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g))) := by ring
    _ = dualWhittakerFn3 W (iotaGL g) *
        (((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
          HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

theorem measurable_phiP [MeasurableSpace G] [BorelSpace G] {W : LocalGL3 v → ℂ} (hWc : Continuous W) {w : G → ℂ}
    (hwc : Continuous w) (s : ℂ) : Measurable (phiP W w s) :=
  ((hWc.comp (continuous_iotaGL v)).mul hwc).measurable.mul (continuous_modC.measurable.pow_const _)

theorem measurable_phiD [MeasurableSpace G] [BorelSpace G] {W : LocalGL3 v → ℂ} (hWc : Continuous W) {w : G → ℂ}
    (hwc : Continuous w) (w₀p : G) (s : ℂ) : Measurable (phiD W w w₀p s) := by
  have h1 : Continuous fun g : G => dualWhittakerFn3 W (iotaGL g) := by
    change Continuous fun g : G => W (longWeyl3 * transposeInv3 (iotaGL g))
    exact hWc.comp (continuous_const.mul ((continuous_transposeInv3 v).comp (continuous_iotaGL v)))
  have h2 : Continuous fun g : G => modC g * w (w₀p * transposeInvN (Fin 2) g) :=
    continuous_modC.mul (hwc.comp (continuous_const.mul (continuous_transposeInvN v)))
  exact (h1.mul h2).measurable.mul (continuous_modC.measurable.pow_const _)

theorem iotaGL_transposeInvN (g : G) : iotaGL (transposeInvN (Fin 2) g) = transposeInv3 (iotaGL g) := by
  refine Units.ext ?_
  change embedMat2 (((g⁻¹ : G) : Mat)ᵀ) = ((((iotaGL g)⁻¹ : G₃)) : Matrix (Fin 3) (Fin 3) F)ᵀ
  rw [← map_inv, coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

theorem phiP_translate (W : LocalGL3 v → ℂ) (w : G → ℂ) (h : G) (s : ℂ) (g : G) :
    phiP (fun x => W (x * (iotaGL h)⁻¹)) w s (g * h) = phiP W (fun x => w (x * h)) s g * modC h ^ (s - 1 / 2) := by
  simp only [phiP, map_mul, mul_inv_cancel_right, modC_cpow_mul]
  ring

theorem phiD_translate (W : LocalGL3 v → ℂ) (w : G → ℂ) (w₀p h : G) (s : ℂ) (g : G) :
    phiD (fun x => W (x * (iotaGL h)⁻¹)) w w₀p s (g * transposeInvN (Fin 2) h) =
      phiD W (fun x => w (x * h)) w₀p s g * (modC (transposeInvN (Fin 2) h) * modC (transposeInvN (Fin 2) h) ^ (s - 1 / 2)) := by
  have hdual : dualWhittakerFn3 (fun x => W (x * (iotaGL h)⁻¹)) (iotaGL (g * transposeInvN (Fin 2) h)) =
      dualWhittakerFn3 W (iotaGL g) := by
    rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, map_mul, transposeInv3_mul, iotaGL_transposeInvN,
      transposeInv3_transposeInv3, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  simp only [phiD]
  rw [hdual, transposeInvN_mul, transposeInvN_transposeInvN, ← mul_assoc w₀p, modC_cpow_mul, modC_mul]
  ring

end Integrands

section LaurentForm

def LF (q : ℂ) (m : ℤ) (P : Polynomial ℂ) (s : ℂ) : ℂ := q ^ ((m : ℂ) * s) * P.eval (q ^ (-s))

theorem LF_def (q : ℂ) (m : ℤ) (P : Polynomial ℂ) (s : ℂ) : LF q m P s = q ^ ((m : ℂ) * s) * P.eval (q ^ (-s)) := rfl

variable {qr : ℝ} (hq : 0 < qr)
include hq

theorem cpow_eq_exp (w : ℂ) : ((qr : ℝ) : ℂ) ^ w = Complex.exp ((Real.log qr : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'), ← Complex.ofReal_log hq.le]

theorem LF_shift (m : ℤ) (n : ℕ) (P : Polynomial ℂ) (s : ℂ) :
    LF ((qr : ℝ) : ℂ) m P s = LF ((qr : ℝ) : ℂ) (m + n) (Polynomial.X ^ n * P) s := by
  rw [LF_def, LF_def, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, cpow_eq_exp hq, cpow_eq_exp hq,
    cpow_eq_exp hq, ← Complex.exp_nat_mul]
  have key : Complex.exp ((Real.log qr : ℂ) * (((m + n : ℤ) : ℂ) * s)) * Complex.exp ((n : ℂ) * ((Real.log qr : ℂ) * -s)) =
      Complex.exp ((Real.log qr : ℂ) * ((m : ℂ) * s)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  calc _ = (Complex.exp ((Real.log qr : ℂ) * (((m + n : ℤ) : ℂ) * s)) * Complex.exp ((n : ℂ) * ((Real.log qr : ℂ) * -s))) *
        Polynomial.eval (Complex.exp ((Real.log qr : ℂ) * -s)) P := by rw [key]
    _ = _ := mul_assoc _ _ _

theorem LF_add (m m' : ℤ) (P P' : Polynomial ℂ) (s : ℂ) :
    LF ((qr : ℝ) : ℂ) m P s + LF ((qr : ℝ) : ℂ) m' P' s =
      LF ((qr : ℝ) : ℂ) (max m m') (Polynomial.X ^ (max m m' - m).toNat * P + Polynomial.X ^ (max m m' - m').toNat * P') s := by
  have h1 := LF_shift hq m (max m m' - m).toNat P s
  have h2 := LF_shift hq m' (max m m' - m').toNat P' s
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr (le_max_left m m')), add_sub_cancel] at h1
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr (le_max_right m m')), add_sub_cancel] at h2
  rw [h1, h2, LF_def, LF_def, LF_def, Polynomial.eval_add]
  ring

omit hq in
theorem LF_const_mul (q : ℂ) (m : ℤ) (P : Polynomial ℂ) (a s : ℂ) :
    a * LF q m P s = LF q m (Polynomial.C a * P) s := by
  rw [LF_def, LF_def, Polynomial.eval_C_mul]; ring

omit hq in
theorem LF_zero (q : ℂ) (s : ℂ) : LF q 0 0 s = 0 := by rw [LF_def, Polynomial.eval_zero, mul_zero]

theorem inv_cpow_mul_LF (k m : ℤ) (P : Polynomial ℂ) (a r s : ℂ) :
    a * (((qr ^ k : ℝ) : ℂ) ^ (s + r))⁻¹ * LF ((qr : ℝ) : ℂ) m P s =
      LF ((qr : ℝ) : ℂ) (m - k) (Polynomial.C (a * Complex.exp (-((k : ℂ) * (Real.log qr : ℂ)) * r)) * P) s := by
  have hb : ((qr ^ k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zpow_ne_zero _ hq.ne')
  have hlog : Complex.log ((qr ^ k : ℝ) : ℂ) = (k : ℂ) * (Real.log qr : ℂ) := by
    rw [← Complex.ofReal_log (zpow_nonneg hq.le _), Real.log_zpow]; push_cast; ring
  rw [Complex.cpow_def_of_ne_zero hb, hlog, ← Complex.exp_neg, LF_def, LF_def, Polynomial.eval_C_mul, cpow_eq_exp hq,
    cpow_eq_exp hq, cpow_eq_exp hq]
  have key : Complex.exp (-((k : ℂ) * (Real.log qr : ℂ) * (s + r))) * Complex.exp ((Real.log qr : ℂ) * ((m : ℂ) * s)) =
      Complex.exp ((Real.log qr : ℂ) * (((m - k : ℤ) : ℂ) * s)) * Complex.exp (-((k : ℂ) * (Real.log qr : ℂ)) * r) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  calc _ = a * (Complex.exp (-((k : ℂ) * (Real.log qr : ℂ) * (s + r))) * Complex.exp ((Real.log qr : ℂ) * ((m : ℂ) * s))) *
        Polynomial.eval (Complex.exp ((Real.log qr : ℂ) * -s)) P := by ring
    _ = a * (Complex.exp ((Real.log qr : ℂ) * (((m - k : ℤ) : ℂ) * s)) * Complex.exp (-((k : ℂ) * (Real.log qr : ℂ)) * r)) *
        Polynomial.eval (Complex.exp ((Real.log qr : ℂ) * -s)) P := by rw [key]
    _ = _ := by ring

end LaurentForm

end RSParentGrowth
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_integrable_and_eq_laurent_of_torusFinite_of_centralChar_of_shellGrowth.RSParentGrowth"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_integrable_and_eq_laurent_of_torusFinite_of_centralChar_of_shellGrowth.RSParentGrowth"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction RSParentGrowth

open scoped nonZeroDivisors ENNReal

set_option maxHeartbeats 3200000 in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)

    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W₃base h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W₃base h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (b : ℕ)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (hβ : ∀ (g₃ : LocalGL3 p) (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ)
      (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η c → c ≤ b →
      letI := localBorel ℚ p
      letI := localGLBorel ℚ p
      haveI := borelSpace_localGLBorel ℚ p
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  W₃base (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 ∧
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                    Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                  dualWhittakerFn3 (fun x => W₃base (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                        (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                        ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0)

    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)

    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂base g)

    (hw₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m))

    (w₀p : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∀ w₂ ∈ Submodule.span ℂ
          (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ W₃ ∈ gl3CyclicSubspace W₃base,
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),

          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (W₃ (iotaGL g) * w₂ g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (dualWhittakerFn3 W₃ (iotaGL g) *
                  (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) :
                        p.adicCompletion ℚ) : ℝ) : ℂ) *
                      w₂ (w₀p * transposeInvN (Fin 2) g)) g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧

          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃ (iotaGL g)) w₂ =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 W₃ (iotaGL g))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) :
                      p.adicCompletion ℚ) : ℝ) : ℂ) *
                    w₂ (w₀p * transposeInvN (Fin 2) g)) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  intro μ₂ _ μN₂ _ w₂ hw₂
  classical
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  haveI := locallyCompactSpace_localGL ℚ p
  haveI := secondCountableTopology_localGL p
  haveI : μN₂.IsMulRightInvariant :=
    ⟨fun g => by
      have : (fun h : ↥(unip p) => h * g) = fun h => g * h := funext fun h => unip_comm p h g
      rw [this]
      exact map_mul_left_eq_self μN₂ g⟩
  set ν : Measure (GL (Fin 2) (p.adicCompletion ℚ)) :=
    μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂) with hν
  have hq : 0 < qR p := qR_pos p
  have hqC : ((qR p : ℝ) : ℂ) = (Ideal.absNorm p.asIdeal : ℂ) := by rw [qR_eq_natCast]; norm_cast

  have hK₁o : IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (p.asIdeal ^ b) (pow_ne_zero b p.ne_bot)).2
  have hw₂sm₀ : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g, w₂base (g * k) = w₂base g := ⟨_, hK₁o, hw₂K⟩
  have hcont2 : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
      fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Continuous w := fun w hw => by
    obtain ⟨U, hU, hfix⟩ := smooth_of_mem_span_translates hw₂sm₀ hw
    exact continuous_of_rightInvariant hU hfix
  have hcont3 : ∀ W ∈ gl3CyclicSubspace W₃base, Continuous W := fun W hW => by
    obtain ⟨U, hU, hfix⟩ := smooth_of_mem_gl3CyclicSubspace hW₃sm hW
    exact continuous_of_rightInvariant hU hfix
  have hw₂c : Continuous w₂base := continuous_of_rightInvariant hK₁o hw₂K

  have hcentralR : ∀ (t : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((ω t : ℂˣ) : ℂ) * w₂base g := by
    intro t g
    have hcomm : g * Matrix.GeneralLinearGroup.scalar (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) t * g := by
      refine Units.ext ?_
      change (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Matrix.scalar (Fin 2) (t : p.adicCompletion ℚ) =
        Matrix.scalar (Fin 2) (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
      exact ((Matrix.scalar_commute (t : p.adicCompletion ℚ) (fun r => mul_comm _ _)
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))).eq).symm
    rw [hcomm, hcentral]

  have hgr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w₂base (diagZ (algebraMap _ (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤ C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m) := hw₂gr

  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_loc p
  haveI : BorelSpace (p.adicCompletion ℚ)ˣ := borelSpace_locUnits p
  haveI := isHaarMeasure_locMul p

  have hbase : ∀ W₃ ∈ gl3CyclicSubspace W₃base,
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
        (∀ s : ℂ, σ₂ < s.re → Integrable (phiP W₃ w₂base s) ν) ∧
        (∀ s : ℂ, σ₃ < s.re → Integrable (phiD W₃ w₂base w₀p s) ν) ∧
        (∀ s : ℂ, σ₂ < s.re → ∫ g, phiP W₃ w₂base s g ∂ν = LF ((qR p : ℝ) : ℂ) m P s) ∧
        (∀ s : ℂ, σ₃ < s.re → ∫ g, phiD W₃ w₂base w₀p s g ∂ν = LF ((qR p : ℝ) : ℂ) md Pd s) := by
    intro W₃ hW₃
    refine Submodule.span_induction (p := fun (W : LocalGL3 p → ℂ) _ =>
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
          (∀ s : ℂ, σ₂ < s.re → Integrable (phiP W w₂base s) ν) ∧
          (∀ s : ℂ, σ₃ < s.re → Integrable (phiD W w₂base w₀p s) ν) ∧
          (∀ s : ℂ, σ₂ < s.re → ∫ g, phiP W w₂base s g ∂ν = LF ((qR p : ℝ) : ℂ) m P s) ∧
          (∀ s : ℂ, σ₃ < s.re → ∫ g, phiD W w₂base w₀p s g ∂ν = LF ((qR p : ℝ) : ℂ) md Pd s)) ?_ ?_ ?_ ?_ hW₃
    ·
      rintro _ ⟨g₃, rfl⟩
      have hmem : gl3AmbientRightTranslate (R := ℂ) g₃ W₃base ∈ gl3CyclicSubspace W₃base := Submodule.subset_span ⟨g₃, rfl⟩
      have hlawg : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (gl3AmbientRightTranslate (R := ℂ) g₃ W₃base) :=
        law_of_mem_gl3CyclicSubspace hW₃law hmem
      have hsmg := smooth_of_mem_gl3CyclicSubspace hW₃sm hmem
      have hgaugeg := (forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3 W₃base hWgauge _ hmem).1

      obtain ⟨σ₂, hσ₂⟩ := LanglandsTunnell.CubicInduction.exists_forall_integrable_rsLocalIntegrand_of_gauge p _ rfl W₃base hW₃law
        hW₃sm hWgauge hπ hϖ b w₂base hw₂law (fun k g hk => hw₂K k hk g) ω hcentralR hgr g₃ μ₂ μN₂
      obtain ⟨σ₃, hσ₃⟩ := LanglandsTunnell.RankinSelberg.exists_forall_integrable_dual_rsLocalIntegrand_of_gauge p _ rfl
        (gl3AmbientRightTranslate (R := ℂ) g₃ W₃base) hlawg hsmg hgaugeg hπ hϖ b w₂base hw₂law (fun k g hk => hw₂K k hk g)
        ω hcentralR hgr w₀p hw₀p μ₂ μN₂
      have hintP : ∀ s : ℂ, σ₂ < s.re → Integrable (phiP (gl3AmbientRightTranslate (R := ℂ) g₃ W₃base) w₂base s) ν :=
        fun s hs => hσ₂ s hs
      have hintD : ∀ s : ℂ, σ₃ < s.re → Integrable (phiD (gl3AmbientRightTranslate (R := ℂ) g₃ W₃base) w₂base w₀p s) ν :=
        fun s hs => hσ₃ s hs

      obtain ⟨P, m, hP⟩ := LanglandsTunnell.RankinSelberg.exists_polynomial_forall_rsLocalIntegral_iotaGL_eq_of_forall_torusShell_localLevelOne_pow_eq_zero
        ℚ p hπ hϖ b (NumberField.StandardAddChar.psiLocal ℚ p) W₃base hW₃law hW₃sm g₃ w₂base hw₂law hw₂K μ₂ μN₂
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        (fun k₀ _ η c hη hc => (hβ g₃ k₀ η c hη hc μ₂).imp fun T hT n hn => (hT n hn).1)
      obtain ⟨Pd, md, hPd⟩ := LanglandsTunnell.RankinSelberg.exists_polynomial_forall_rsLocalIntegral_dualWhittakerFn3_iotaGL_eq_of_forall_torusShell_transposeInvN_eq_zero
        ℚ p hπ hϖ b (NumberField.StandardAddChar.psiLocal ℚ p) W₃base hW₃law hW₃sm g₃ w₂base hw₂law hw₂K w₀p hw₀p μ₂ μN₂
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        (fun k₀ _ η c hη hc => (hβ g₃ k₀ η c hη hc μ₂).imp fun T hT n hn => (hT n hn).2)
      refine ⟨P, Pd, m, md, σ₂, σ₃, hintP, hintD, fun s hs => ?_, fun s hs => ?_⟩
      · have h := hP s (hintP s hs)
        rw [← hqC, ← LF_def] at h
        exact h
      · have h := hPd s (hintD s hs)
        rw [← hqC, ← LF_def] at h
        exact h
    ·
      refine ⟨0, 0, 0, 0, 0, 0, fun s _ => ?_, fun s _ => ?_, fun s _ => ?_, fun s _ => ?_⟩
      · have : phiP (0 : LocalGL3 p → ℂ) w₂base s = 0 := by funext g; simp [phiP]
        rw [this]; exact integrable_zero _ _ _
      · have : phiD (0 : LocalGL3 p → ℂ) w₂base w₀p s = 0 := by funext g; simp [phiD, dualWhittakerFn3_apply]
        rw [this]; exact integrable_zero _ _ _
      · have : phiP (0 : LocalGL3 p → ℂ) w₂base s = 0 := by funext g; simp [phiP]
        rw [this, LF_zero]; simp
      · have : phiD (0 : LocalGL3 p → ℂ) w₂base w₀p s = 0 := by funext g; simp [phiD, dualWhittakerFn3_apply]
        rw [this, LF_zero]; simp
    ·
      intro W W' _ _ hPW hPW'
      obtain ⟨P, Pd, m, md, σ₂, σ₃, h1, h2, h3, h4⟩ := hPW
      obtain ⟨P', Pd', m', md', σ₂', σ₃', h1', h2', h3', h4'⟩ := hPW'
      have haddP : ∀ s, phiP (W + W') w₂base s = fun g => phiP W w₂base s g + phiP W' w₂base s g := by
        intro s; funext g; simp only [phiP, Pi.add_apply]; ring
      have haddD : ∀ s, phiD (W + W') w₂base w₀p s = fun g => phiD W w₂base w₀p s g + phiD W' w₂base w₀p s g := by
        intro s; funext g; simp only [phiD, dualWhittakerFn3_apply, Pi.add_apply]; ring
      refine ⟨Polynomial.X ^ (max m m' - m).toNat * P + Polynomial.X ^ (max m m' - m').toNat * P',
        Polynomial.X ^ (max md md' - md).toNat * Pd + Polynomial.X ^ (max md md' - md').toNat * Pd',
        max m m', max md md', max σ₂ σ₂', max σ₃ σ₃',
        fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
      · rw [haddP s]; exact (h1 s ((le_max_left _ _).trans_lt hs)).add (h1' s ((le_max_right _ _).trans_lt hs))
      · rw [haddD s]; exact (h2 s ((le_max_left _ _).trans_lt hs)).add (h2' s ((le_max_right _ _).trans_lt hs))
      · rw [haddP s, integral_add (h1 s ((le_max_left _ _).trans_lt hs)) (h1' s ((le_max_right _ _).trans_lt hs)),
          h3 s ((le_max_left _ _).trans_lt hs), h3' s ((le_max_right _ _).trans_lt hs), LF_add hq]
      · rw [haddD s, integral_add (h2 s ((le_max_left _ _).trans_lt hs)) (h2' s ((le_max_right _ _).trans_lt hs)),
          h4 s ((le_max_left _ _).trans_lt hs), h4' s ((le_max_right _ _).trans_lt hs), LF_add hq]
    ·
      intro c W _ hPW
      obtain ⟨P, Pd, m, md, σ₂, σ₃, h1, h2, h3, h4⟩ := hPW
      have hsmP : ∀ s, phiP (c • W) w₂base s = fun g => c * phiP W w₂base s g := by
        intro s; funext g; simp only [phiP, Pi.smul_apply, smul_eq_mul]; ring
      have hsmD : ∀ s, phiD (c • W) w₂base w₀p s = fun g => c * phiD W w₂base w₀p s g := by
        intro s; funext g; simp only [phiD, dualWhittakerFn3_apply, Pi.smul_apply, smul_eq_mul]; ring
      refine ⟨Polynomial.C c * P, Polynomial.C c * Pd, m, md, σ₂, σ₃,
        fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
      · rw [hsmP s]; exact (h1 s hs).const_mul c
      · rw [hsmD s]; exact (h2 s hs).const_mul c
      · rw [hsmP s, integral_const_mul, h3 s hs, LF_const_mul]
      · rw [hsmD s, integral_const_mul, h4 s hs, LF_const_mul]

  let Pack : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) → Prop := fun w =>
    ∀ W₃ ∈ gl3CyclicSubspace W₃base,
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
        (∀ s : ℂ, σ₂ < s.re → Integrable (phiP W₃ w s) ν) ∧
        (∀ s : ℂ, σ₃ < s.re → Integrable (phiD W₃ w w₀p s) ν) ∧
        (∀ s : ℂ, σ₂ < s.re → ∫ g, phiP W₃ w s g ∂ν = LF ((qR p : ℝ) : ℂ) m P s) ∧
        (∀ s : ℂ, σ₃ < s.re → ∫ g, phiD W₃ w w₀p s g ∂ν = LF ((qR p : ℝ) : ℂ) md Pd s)
  suffices hPack : Pack w₂ by
    intro W₃ hW₃
    obtain ⟨P, Pd, m, md, σ₂, σ₃, h1, h2, h3, h4⟩ := hPack W₃ hW₃
    refine ⟨P, Pd, m, md, σ₂, σ₃, h1, h2, fun s hs => ?_, fun s hs => ?_⟩
    · have := h3 s hs
      rw [LF_def, hqC] at this
      exact this
    · have := h4 s hs
      rw [LF_def, hqC] at this
      exact this
  refine Submodule.span_induction (p := fun w _ => Pack w) ?_ ?_ ?_ ?_ hw₂
  ·
    rintro _ ⟨h, rfl⟩ W₃ hW₃

    set W₃' : LocalGL3 p → ℂ := fun x => W₃ (x * (iotaGL h)⁻¹) with hW₃'
    have hW₃'mem : W₃' ∈ gl3CyclicSubspace W₃base := gl3AmbientRightTranslate_mem_gl3CyclicSubspace W₃base _ hW₃
    obtain ⟨P, Pd, m, md, σ₂, σ₃, hint, hintd, hval', hvald'⟩ := hbase W₃' hW₃'mem

    have hlaw' : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃' := law_of_mem_gl3CyclicSubspace hW₃law hW₃'mem
    have hW₃'c : Continuous W₃' := hcont3 _ hW₃'mem
    have hmP : ∀ s, Measurable (phiP W₃' w₂base s) := fun s => measurable_phiP hW₃'c hw₂c s
    have hmD : ∀ s, Measurable (phiD W₃' w₂base w₀p s) := fun s => measurable_phiD hW₃'c hw₂c w₀p s
    have hNP : ∀ s, ∀ (x : ↥(unip p)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        phiP W₃' w₂base s ((x : GL (Fin 2) (p.adicCompletion ℚ)) * g) = phiP W₃' w₂base s g :=
      fun s => phiP_unipotent_mul hlaw' hw₂law s
    have hND : ∀ s, ∀ (x : ↥(unip p)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        phiD W₃' w₂base w₀p s ((x : GL (Fin 2) (p.adicCompletion ℚ)) * g) = phiD W₃' w₂base w₀p s g :=
      fun s => phiD_unipotent_mul hlaw' hw₂law hw₀p s

    obtain ⟨c₁, hc₁0, hc₁⟩ := HaarQuotient.exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul (E := ℂ) μ₂
      (unipotentGL2Hom (R := p.adicCompletion ℚ)).range (isClosed_unip p) μN₂ h
    obtain ⟨c₂, hc₂0, hc₂⟩ := HaarQuotient.exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul (E := ℂ) μ₂
      (unipotentGL2Hom (R := p.adicCompletion ℚ)).range (isClosed_unip p) μN₂ (transposeInvN (Fin 2) h)

    obtain ⟨k₁, hk₁⟩ := exists_modulus_det_eq_zpow p h
    obtain ⟨k₂, hk₂⟩ := exists_modulus_det_eq_zpow p (transposeInvN (Fin 2) h)
    have hB₁ : (modC h : ℂ) = ((qR p ^ k₁ : ℝ) : ℂ) := by rw [modC, hk₁]
    have hB₂ : (modC (transposeInvN (Fin 2) h) : ℂ) = ((qR p ^ k₂ : ℝ) : ℂ) := by rw [modC, hk₂]

    have hΦP : ∀ s, phiP W₃ (fun x => w₂base (x * h)) s =
        fun g => phiP W₃' w₂base s (g * h) * (modC h ^ (s - 1 / 2))⁻¹ := by
      intro s; funext g
      rw [phiP_translate, mul_assoc, mul_inv_cancel₀, mul_one]
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl (modC_ne_zero h))
    have hΦD : ∀ s, phiD W₃ (fun x => w₂base (x * h)) w₀p s =
        fun g => phiD W₃' w₂base w₀p s (g * transposeInvN (Fin 2) h) *
          (modC (transposeInvN (Fin 2) h) * modC (transposeInvN (Fin 2) h) ^ (s - 1 / 2))⁻¹ := by
      intro s; funext g
      rw [phiD_translate, mul_assoc, mul_inv_cancel₀, mul_one]
      exact mul_ne_zero (modC_ne_zero _) (Complex.cpow_ne_zero_iff.mpr (Or.inl (modC_ne_zero _)))

    have hB₂pow : ∀ s : ℂ, modC (transposeInvN (Fin 2) h) * modC (transposeInvN (Fin 2) h) ^ (s - 1 / 2) =
        ((qR p ^ k₂ : ℝ) : ℂ) ^ (s + 1 / 2) := by
      intro s
      have hb : ((qR p ^ k₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zpow_ne_zero _ hq.ne')
      rw [hB₂, show s + 1 / 2 = 1 + (s - 1 / 2) by ring, Complex.cpow_add _ _ hb, Complex.cpow_one]
    refine ⟨Polynomial.C ((c₁ : ℂ) * Complex.exp (-((k₁ : ℂ) * (Real.log (qR p) : ℂ)) * (-1 / 2))) * P,
      Polynomial.C ((c₂ : ℂ) * Complex.exp (-((k₂ : ℂ) * (Real.log (qR p) : ℂ)) * (1 / 2))) * Pd,
      m - k₁, md - k₂, σ₂, σ₃, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
    · rw [hΦP s]
      exact (((hc₁ _ (hmP s) (hNP s)).1.mpr (hint s hs)).mul_const _)
    · rw [hΦD s]
      exact (((hc₂ _ (hmD s) (hND s)).1.mpr (hintd s hs)).mul_const _)
    · rw [hΦP s, integral_mul_const, (hc₁ _ (hmP s) (hNP s)).2, hval' s hs, hB₁, Complex.real_smul,
        show s - 1 / 2 = s + (-1 / 2 : ℂ) by ring, mul_comm, ← mul_assoc, mul_comm _ ((c₁ : ℝ) : ℂ)]
      exact inv_cpow_mul_LF hq k₁ m P (c₁ : ℂ) (-1 / 2) s
    · rw [hΦD s, integral_mul_const, (hc₂ _ (hmD s) (hND s)).2, hvald' s hs, hB₂pow s, Complex.real_smul, mul_comm,
        ← mul_assoc, mul_comm _ ((c₂ : ℝ) : ℂ)]
      exact inv_cpow_mul_LF hq k₂ md Pd (c₂ : ℂ) (1 / 2) s
  ·
    intro W₃ hW₃
    refine ⟨0, 0, 0, 0, 0, 0, fun s _ => ?_, fun s _ => ?_, fun s _ => ?_, fun s _ => ?_⟩
    · have : phiP W₃ (0 : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) s = 0 := by funext g; simp [phiP]
      rw [this]; exact integrable_zero _ _ _
    · have : phiD W₃ (0 : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) w₀p s = 0 := by funext g; simp [phiD]
      rw [this]; exact integrable_zero _ _ _
    · have : phiP W₃ (0 : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) s = 0 := by funext g; simp [phiP]
      rw [this, LF_zero]; simp
    · have : phiD W₃ (0 : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) w₀p s = 0 := by funext g; simp [phiD]
      rw [this, LF_zero]; simp
  ·
    intro w w' _ _ hPw hPw' W₃ hW₃
    obtain ⟨P, Pd, m, md, σ₂, σ₃, h1, h2, h3, h4⟩ := hPw W₃ hW₃
    obtain ⟨P', Pd', m', md', σ₂', σ₃', h1', h2', h3', h4'⟩ := hPw' W₃ hW₃
    have haddP : ∀ s, phiP W₃ (w + w') s = fun g => phiP W₃ w s g + phiP W₃ w' s g := by
      intro s; funext g; simp only [phiP, Pi.add_apply]; ring
    have haddD : ∀ s, phiD W₃ (w + w') w₀p s = fun g => phiD W₃ w w₀p s g + phiD W₃ w' w₀p s g := by
      intro s; funext g; simp only [phiD, Pi.add_apply]; ring
    refine ⟨Polynomial.X ^ (max m m' - m).toNat * P + Polynomial.X ^ (max m m' - m').toNat * P',
      Polynomial.X ^ (max md md' - md).toNat * Pd + Polynomial.X ^ (max md md' - md').toNat * Pd',
      max m m', max md md', max σ₂ σ₂', max σ₃ σ₃',
      fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
    · rw [haddP s]; exact (h1 s ((le_max_left _ _).trans_lt hs)).add (h1' s ((le_max_right _ _).trans_lt hs))
    · rw [haddD s]; exact (h2 s ((le_max_left _ _).trans_lt hs)).add (h2' s ((le_max_right _ _).trans_lt hs))
    · rw [haddP s, integral_add (h1 s ((le_max_left _ _).trans_lt hs)) (h1' s ((le_max_right _ _).trans_lt hs)),
        h3 s ((le_max_left _ _).trans_lt hs), h3' s ((le_max_right _ _).trans_lt hs), LF_add hq]
    · rw [haddD s, integral_add (h2 s ((le_max_left _ _).trans_lt hs)) (h2' s ((le_max_right _ _).trans_lt hs)),
        h4 s ((le_max_left _ _).trans_lt hs), h4' s ((le_max_right _ _).trans_lt hs), LF_add hq]
  ·
    intro c w _ hPw W₃ hW₃
    obtain ⟨P, Pd, m, md, σ₂, σ₃, h1, h2, h3, h4⟩ := hPw W₃ hW₃
    have hsmP : ∀ s, phiP W₃ (c • w) s = fun g => c * phiP W₃ w s g := by
      intro s; funext g; simp only [phiP, Pi.smul_apply, smul_eq_mul]; ring
    have hsmD : ∀ s, phiD W₃ (c • w) w₀p s = fun g => c * phiD W₃ w w₀p s g := by
      intro s; funext g; simp only [phiD, Pi.smul_apply, smul_eq_mul]; ring
    refine ⟨Polynomial.C c * P, Polynomial.C c * Pd, m, md, σ₂, σ₃,
      fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
    · rw [hsmP s]; exact (h1 s hs).const_mul c
    · rw [hsmD s]; exact (h2 s hs).const_mul c
    · rw [hsmP s, integral_const_mul, h3 s hs, LF_const_mul]
    · rw [hsmD s, integral_const_mul, h4 s hs, LF_const_mul]

end S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_integrable_and_eq_laurent_of_torusFinite_of_centralChar_of_shellGrowth
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral_integrable_and_eq_laurent_of_torusFinite_of_centralChar_of_shellGrowth (solution)
