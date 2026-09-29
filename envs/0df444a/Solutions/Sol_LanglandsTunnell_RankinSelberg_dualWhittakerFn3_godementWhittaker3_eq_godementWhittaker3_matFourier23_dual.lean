-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/8ddfafc8-7200-5f32-a77a-4b924cccddf8

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_HaarQuotient
import Theorems.Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_CubicInduction_integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame
import Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_and_law_matFourier23_dualDatum
import Theorems.Thm_AutomorphicForm_map_transposeInvN_eq_self_of_isHaarMeasure_fin_two
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier23_comp_mul_mul_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction NumberField.StandardAddChar

open scoped ENNReal NNReal Pointwise

noncomputable section

namespace B2Asm

section LocalField

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem norm_units_pos (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : 0 < ‖(u : F)‖ :=
  norm_pos_iff.mpr u.ne_zero

scoped instance secondCountable_units : SecondCountableTopology (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm p.asIdeal : ℝ≥0) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm p.asIdeal : ℝ≥0) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure F)).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

end LocalField

section GL2

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion ℚ p))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G := locallyCompactSpace_localGL ℚ p

theorem continuous_entry (i j : Fin 2) : Continuous fun g : G => (g : Mat) i j :=
  (Units.continuous_val).matrix_elem i j

theorem continuous_row (i : Fin 2) : Continuous fun g : G => (g : Mat) i :=
  continuous_pi fun j => continuous_entry p i j

abbrev unip : Subgroup G := (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ p)).range

theorem coe_unip_eq :
    ((unip p : Subgroup G) : Set G) = {g : G | (g : Mat) 0 0 = 1 ∧ (g : Mat) 1 0 = 0 ∧ (g : Mat) 1 1 = 1} := by
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

theorem isClosed_unip : IsClosed ((unip p : Subgroup G) : Set G) := by
  rw [coe_unip_eq]
  exact ((isClosed_singleton.preimage (continuous_entry p 0 0)).inter
    ((isClosed_singleton.preimage (continuous_entry p 1 0)).inter
      (isClosed_singleton.preimage (continuous_entry p 1 1))))

theorem unip_eq_unipotentGL2 (n : unip p) : (n : G) = unipotentGL2 (((n : G) : Mat) 0 1) := by
  obtain ⟨z, hz⟩ := n.2
  rw [← hz]
  change (unipotentGL2 z.toAdd : G) = unipotentGL2 (((unipotentGL2 z.toAdd : G) : Mat) 0 1)
  have h01 : (((unipotentGL2 z.toAdd : G) : Mat) 0 1) = z.toAdd := by simp [unipotentGL2_coe]
  rw [h01]

theorem unip_comm (m n : unip p) : m * n = n * m := by
  refine Subtype.ext ?_
  change (m : G) * (n : G) = (n : G) * (m : G)
  rw [unip_eq_unipotentGL2 p m, unip_eq_unipotentGL2 p n, ← unipotentGL2_add, ← unipotentGL2_add, add_comm]

theorem det_unipotentGL2 (x : F) : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem row_unipotentGL2_mul (x : F) (g : G) : (((unipotentGL2 x * g : G)) : Mat) 1 = (g : Mat) 1 := by
  funext j
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe]

theorem continuous_unipotentGL2 : Continuous fun y : F => (unipotentGL2 y : G) := by
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ fun y : F => (unipotentGL2 y : G)) = fun y => !![1, y; 0, 1] := funext fun y => rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id
  · have h : (fun y : F => (((unipotentGL2 y : G)⁻¹ : G) : Mat)) = fun y => !![1, -y; 0, 1] :=
      funext fun y => rfl
    show Continuous fun y : F => (((unipotentGL2 y : G)⁻¹ : G) : Mat)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_neg

def unipHomeo : F ≃ₜ (unip p) where
  toFun y := ⟨unipotentGL2 y, ⟨Multiplicative.ofAdd y, rfl⟩⟩
  invFun n := ((n : G) : Mat) 0 1
  left_inv y := by simp [unipotentGL2_coe]
  right_inv n := Subtype.ext (unip_eq_unipotentGL2 p n).symm
  continuous_toFun := (continuous_unipotentGL2 p).subtype_mk _
  continuous_invFun := (continuous_entry p 0 1).comp continuous_subtype_val

theorem unipHomeo_apply_coe (y : F) : ((unipHomeo p y : unip p) : G) = unipotentGL2 y := rfl

theorem unipHomeo_add (y y' : F) : unipHomeo p (y + y') = unipHomeo p y * unipHomeo p y' :=
  Subtype.ext (by simp [unipHomeo_apply_coe, unipotentGL2_add])

theorem continuous_modulus_det :
    Continuous fun g : G =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) := by
  have : (fun g : G => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) :
      ℝ) : ℂ)) = fun g : G => ((‖(g : Mat).det‖ : ℝ) : ℂ) := by
    funext g
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))

end GL2

section SubgroupHaar

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

scoped instance borelSpace_units_local : BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)ˣ := borelSpace_units

scoped instance locallyCompactSpace_unip : LocallyCompactSpace (unip p) := (isClosed_unip p).locallyCompactSpace

scoped instance secondCountable_unip : SecondCountableTopology (unip p) :=
  TopologicalSpace.Subtype.secondCountableTopology ((unip p : Subgroup G) : Set G)

theorem isMulRightInvariant_unip (μN : Measure (unip p)) [μN.IsMulLeftInvariant] : μN.IsMulRightInvariant := by
  refine ⟨fun n₀ => ?_⟩
  have h : (fun n : unip p => n * n₀) = fun n => n₀ * n := funext fun n => unip_comm p n n₀
  rw [h]
  exact map_mul_left_eq_self μN n₀

def unipMeasure (ν : Measure F) : Measure (unip p) := Measure.map (unipHomeo p) ν

theorem measurable_unipHomeo : Measurable (unipHomeo p) := (unipHomeo p).continuous.measurable

scoped instance isHaarMeasure_unipMeasure (ν : Measure F) [ν.IsAddHaarMeasure] : (unipMeasure p ν).IsHaarMeasure where
  map_mul_left_eq_self n₀ := by
    obtain ⟨y₀, rfl⟩ : ∃ y₀, unipHomeo p y₀ = n₀ := ⟨(unipHomeo p).symm n₀, (unipHomeo p).apply_symm_apply n₀⟩
    unfold unipMeasure
    rw [Measure.map_map (measurable_const_mul _) (measurable_unipHomeo p)]
    have hcomp : ((fun n : unip p => unipHomeo p y₀ * n) ∘ (unipHomeo p)) = (unipHomeo p) ∘ fun y : F => y₀ + y := by
      funext y
      simp [Function.comp_apply, unipHomeo_add]
    rw [hcomp, ← Measure.map_map (measurable_unipHomeo p) (measurable_const_add _), map_add_left_eq_self]
  lt_top_of_isCompact K hK := by
    unfold unipMeasure
    rw [Measure.map_apply (measurable_unipHomeo p) hK.measurableSet]
    have : (unipHomeo p) ⁻¹' K = (unipHomeo p).symm '' K := by
      rw [← Homeomorph.image_symm]
    rw [this]
    exact (hK.image (unipHomeo p).symm.continuous).measure_lt_top
  open_pos U hU hne := by
    unfold unipMeasure
    rw [Measure.map_apply (measurable_unipHomeo p) hU.measurableSet]
    exact (hU.preimage (unipHomeo p).continuous).measure_ne_zero ν (hne.preimage (unipHomeo p).surjective)

theorem exists_eq_smul_unipMeasure (ν : Measure F) [ν.IsAddHaarMeasure] (μN : Measure (unip p)) [μN.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ μN = c • unipMeasure p ν :=
  ⟨μN.haarScalarFactor (unipMeasure p ν), Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
    Measure.isMulLeftInvariant_eq_smul _ _⟩

theorem integral_unip_eq (ν : Measure F) [ν.IsAddHaarMeasure] (μN : Measure (unip p)) [μN.IsHaarMeasure]
    {c : ℝ≥0} (hc : μN = c • unipMeasure p ν) (h : unip p → ℂ) :
    ∫ n, h n ∂μN = (c : ℂ) * ∫ y, h (unipHomeo p y) ∂ν := by
  rw [hc, integral_smul_nnreal_measure]
  unfold unipMeasure
  rw [← Homeomorph.toMeasurableEquiv_coe, integral_map_equiv]
  rw [NNReal.smul_def, Complex.real_smul]

end SubgroupHaar

section Unfold

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem integrable_and_integral_eq_unfold
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Φ : G → ℂ) (hΦm : Measurable Φ) (hΦi : Integrable Φ μ) :
    (∀ᵐ g ∂(μ.withDensity (HaarQuotient.density H μH)), Integrable (fun x : H => Φ ((x : G) * g)) μH) ∧
    Integrable (fun g : G => ∫ x : H, Φ ((x : G) * g) ∂μH) (μ.withDensity (HaarQuotient.density H μH)) ∧
    ∫ g, Φ g ∂μ = ∫ g, (∫ x : H, Φ ((x : G) * g) ∂μH) ∂(μ.withDensity (HaarQuotient.density H μH)) := by
  classical

  have hS : IsFundamentalDomain (↥(⊥ : Subgroup G)) (Set.univ : Set G) μ :=
    ⟨MeasurableSet.univ.nullMeasurableSet, Filter.Eventually.of_forall fun x => ⟨1, Set.mem_univ _⟩,
      Subsingleton.pairwise⟩
  haveI : Subsingleton (↥((⊥ : Subgroup G).subgroupOf H)) := ⟨fun a b => by
    refine Subtype.ext (Subtype.ext ?_)
    have ha := a.2
    have hb := b.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at ha hb
    rw [ha, hb]⟩
  have hT : IsFundamentalDomain (↥((⊥ : Subgroup G).subgroupOf H)) (Set.univ : Set H) μH :=
    ⟨MeasurableSet.univ.nullMeasurableSet, Filter.Eventually.of_forall fun x => ⟨1, Set.mem_univ _⟩,
      Subsingleton.pairwise⟩
  have hfin : ∫⁻ g in Set.univ, ‖Φ g‖ₑ ∂μ < ⊤ := by
    rw [Measure.restrict_univ]
    exact hΦi.2
  obtain ⟨h1, h2, h3⟩ :=
    HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out μ H hH μH ⊥ bot_le Φ
      hΦm (fun γ hγ g => by rw [Subgroup.mem_bot.mp hγ, one_mul]) Set.univ hS Set.univ hT hfin
  simp only [Measure.restrict_univ] at h2 h3
  simp only [integrableOn_univ] at h1

  set μD := μ.withDensity (HaarQuotient.density H μH) with hμD
  set Ξ : MulAction.orbitRel.Quotient H G → ℂ := fun q => ∫ x : H, Φ ((x : G) * q.out) ∂μH with hΞ
  have hmk : Measurable (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) := measurable_quotient_mk''
  have hmeas : HaarQuotient.measure μ H μH = Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) μD :=
    rfl
  rw [hmeas] at h1 h2 h3
  have hΞi : Integrable Ξ (Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) μD) := h2
  have hcomp : Integrable (Ξ ∘ (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)) μD :=
    (integrable_map_measure hΞi.aestronglyMeasurable hmk.aemeasurable).mp hΞi
  have hint : ∫ q, Ξ q ∂(Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) μD) =
      ∫ g, Ξ (Quotient.mk'' g) ∂μD :=
    integral_map hmk.aemeasurable hΞi.aestronglyMeasurable

  have hfib : ∀ g : G, Ξ (Quotient.mk'' g) = ∫ x : H, Φ ((x : G) * g) ∂μH := by
    intro g
    have hrel : @Setoid.r _ (MulAction.orbitRel H G) ((Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) g :=
      Quotient.mk_out' g
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨n, hn⟩ := hrel
    simp only [hΞ]
    rw [← hn, Subgroup.smul_def, smul_eq_mul]
    have := integral_mul_right_eq_self (μ := μH) (fun x : H => Φ ((x : G) * g)) n
    simpa only [Subgroup.coe_mul, mul_assoc] using this
  have hfun : (Ξ ∘ (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)) = fun g => ∫ x : H, Φ ((x : G) * g) ∂μH :=
    funext fun g => hfib g

  have hae : ∀ᵐ g ∂μD, Integrable (fun x : H => Φ ((x : G) * g)) μH := by
    have h1' := ae_of_ae_map hmk.aemeasurable h1
    filter_upwards [h1'] with g hg
    have hrel : @Setoid.r _ (MulAction.orbitRel H G) ((Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) g :=
      Quotient.mk_out' g
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨n, hn⟩ := hrel
    rw [← hn, Subgroup.smul_def, smul_eq_mul] at hg
    have := hg.comp_mul_right n⁻¹
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left]
  refine ⟨hae, hfun ▸ hcomp, ?_⟩
  rw [h3, hint]
  exact integral_congr_ae (Filter.Eventually.of_forall hfib)

end Unfold

end B2Asm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual.B2Asm"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual.B2Asm"

noncomputable section

open scoped Matrix

namespace B2Asm

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat3" => (Matrix (Fin 3) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "M23" => (Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem level_zero :
    (∀ x : F, Valued.v x ≤ WithZero.exp (0 : ℤ) → psiLocal ℚ p x = 1) ∧
      ∃ x : F, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ psiLocal ℚ p x ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : F, Valued.v x ≤ WithZero.exp k → psiLocal ℚ p x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p
    (psiLocal ℚ p) hk (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h

theorem level_zero_inv :
    (∀ x : F, Valued.v x ≤ WithZero.exp (0 : ℤ) → (psiLocal ℚ p)⁻¹ x = 1) ∧
      ∃ x : F, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ (psiLocal ℚ p)⁻¹ x ≠ 1 := by
  obtain ⟨h0, h1⟩ := level_zero p
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [AddChar.inv_apply]; exact h0 (-x) (by rwa [Valuation.map_neg])
  · obtain ⟨x, hx, hne⟩ := h1
    refine ⟨-x, by rwa [Valuation.map_neg], ?_⟩
    rwa [AddChar.inv_apply, neg_neg]

theorem levels (η : AddChar F ℂ) (hη : η = psiLocal ℚ p ∨ η = (psiLocal ℚ p)⁻¹) :
    ((∀ x : F, Valued.v x ≤ WithZero.exp (0 : ℤ) → η x = 1) ∧
      ∃ x : F, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ η x ≠ 1) ∧
    ((∀ x : F, Valued.v x ≤ WithZero.exp (0 : ℤ) → η⁻¹ x = 1) ∧
      ∃ x : F, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ η⁻¹ x ≠ 1) := by
  rcases hη with rfl | rfl
  · exact ⟨level_zero p, level_zero_inv p⟩
  · rw [inv_inv]; exact ⟨level_zero_inv p, level_zero p⟩

theorem coe_transposeInvN_inv (k : G) : ((transposeInvN (Fin 2) k⁻¹ : G) : Mat) = ((k : G) : Mat)ᵀ := by
  rw [coe_transposeInvN, inv_inv]

theorem transposeInvN_transposeInv3 (g : GL (Fin 3) F) : transposeInvN (Fin 3) (transposeInv3 g) = g := by
  apply Units.ext
  rw [coe_transposeInvN]
  show (((transposeInv3 g)⁻¹ : GL (Fin 3) F) : Mat3)ᵀ = (g : Mat3)
  have : (((transposeInv3 g)⁻¹ : GL (Fin 3) F) : Mat3) = ((g : GL (Fin 3) F) : Mat3)ᵀ := rfl
  rw [this, Matrix.transpose_transpose]

theorem coe_transposeInv3 (g : GL (Fin 3) F) : ((transposeInv3 g : GL (Fin 3) F) : Mat3) = (((g⁻¹ : GL (Fin 3) F)) : Mat3)ᵀ := rfl

theorem frame_mul_longWeyl3 (t : F × F × F) :
    (!![1, t.1, t.2.1; 0, 1, t.2.2] : M23) * ((longWeyl3 : GL (Fin 3) F) : Mat3) = !![t.2.1, t.1, 1; t.2.2, 1, 0] := by
  have hw : ((longWeyl3 : GL (Fin 3) F) : Mat3) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  rw [hw]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem w2_mul_frame (t : F × F × F) :
    (!![0, 1; 1, 0] : Mat) * (!![1, t.1, t.2.1; 0, 1, t.2.2] : M23) = !![0, 1, t.2.2; 1, t.1, t.2.1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem transposeInvN_unipotent_mul_w2 (w₂ : G) (hw₂ : ((w₂ : G) : Mat) = !![0, 1; 1, 0]) (a : F) :
    transposeInvN (Fin 2) (unipotentGL2 (-a)) * w₂ = w₂ * unipotentGL2 a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_transposeInvN, hw₂]
  have : (((unipotentGL2 (-a) : G)⁻¹ : G) : Mat) = !![1, a; 0, 1] := by
    show (!![1, -(-a); 0, 1] : Mat) = !![1, a; 0, 1]
    rw [neg_neg]
  rw [this, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_unipotentGL2' (a : F) : Matrix.GeneralLinearGroup.det (unipotentGL2 a : G) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem det_w2 (w₂ : G) (hw₂ : ((w₂ : G) : Mat) = !![0, 1; 1, 0]) :
    ((Matrix.GeneralLinearGroup.det w₂ : Fˣ) : F) = -1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, hw₂, Matrix.det_fin_two_of]; ring

theorem det_longWeyl3 : ((Matrix.GeneralLinearGroup.det (longWeyl3 : GL (Fin 3) F) : Fˣ) : F) = -1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have hw : ((longWeyl3 : GL (Fin 3) F) : Mat3) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  rw [hw, Matrix.det_fin_three]
  simp

theorem det_transposeInvN (k : G) :
    ((Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) k) : Fˣ) : F) =
      (((Matrix.GeneralLinearGroup.det k : Fˣ) : F))⁻¹ := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInvN, Matrix.det_transpose,
    ← Matrix.GeneralLinearGroup.val_det_apply, ← Units.val_inv_eq_inv_val, map_inv]

theorem det_transposeInv3 (g : GL (Fin 3) F) :
    ((Matrix.GeneralLinearGroup.det (transposeInv3 g) : Fˣ) : F) =
      (((Matrix.GeneralLinearGroup.det g : Fˣ) : F))⁻¹ := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInv3]
  rw [Matrix.det_transpose, ← Matrix.GeneralLinearGroup.val_det_apply, ← Units.val_inv_eq_inv_val, map_inv]

theorem w2_mul_w2 (w₂ : G) (hw₂ : ((w₂ : G) : Mat) = !![0, 1; 1, 0]) : w₂ * w₂ = 1 := by
  apply Units.ext
  rw [Units.val_mul, hw₂, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem transposeInvN_w2 (w₂ : G) (hw₂ : ((w₂ : G) : Mat) = !![0, 1; 1, 0]) : transposeInvN (Fin 2) w₂ = w₂ := by
  have hinv : w₂⁻¹ = w₂ := inv_eq_of_mul_eq_one_left (w2_mul_w2 p w₂ hw₂)
  apply Units.ext
  rw [coe_transposeInvN, hinv, hw₂]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

scoped instance isNegInvariant_selfDual : (selfDualHaarAt ℚ p : Measure F).IsNegInvariant := by
  haveI := isAddHaarMeasure_selfDualHaarAt p
  haveI : (selfDualHaarAt ℚ p : Measure F).Regular := by
    show ((((Ideal.absNorm p.asIdeal : ℝ≥0) ^
        (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2))
        • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure F)).Regular
    rw [ENNReal.smul_def]
    exact Measure.Regular.smul ENNReal.coe_ne_top
  exact Measure.IsAddHaarMeasure.isNegInvariant_of_regular _

end B2Asm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual.B2Asm"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual.B2Asm"

noncomputable section

namespace B2Asm

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem unfold_unip (μ₂ : Measure G) [μ₂.IsHaarMeasure] (Ψ : G → ℂ) (hΨ : Integrable Ψ μ₂) :
    ∫ k, Ψ k ∂μ₂ =
      ∫ k, (∫ a : F, Ψ (unipotentGL2 a * k) ∂(selfDualHaarAt ℚ p))
        ∂(μ₂.withDensity (HaarQuotient.density (unip p) (unipMeasure p (selfDualHaarAt ℚ p)))) := by
  haveI : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  set ν : Measure F := selfDualHaarAt ℚ p with hν
  set μN : Measure (unip p) := unipMeasure p ν with hμN
  haveI : μN.IsMulRightInvariant := isMulRightInvariant_unip p μN
  have hμN1 : μN = (1 : ℝ≥0) • unipMeasure p ν := by rw [one_smul]
  set μD := μ₂.withDensity (HaarQuotient.density (unip p) μN) with hμD

  set Ψ' : G → ℂ := hΨ.1.mk Ψ with hΨ'
  have hΨ'm : Measurable Ψ' := hΨ.1.stronglyMeasurable_mk.measurable
  have hae : Ψ =ᵐ[μ₂] Ψ' := hΨ.1.ae_eq_mk
  have hΨ'i : Integrable Ψ' μ₂ := hΨ.congr hae
  obtain ⟨-, -, hunf⟩ := integrable_and_integral_eq_unfold μ₂ (unip p) (isClosed_unip p) μN Ψ' hΨ'm hΨ'i

  obtain ⟨T, hTsub, hTm, hT0⟩ : ∃ T : Set G, {x | Ψ x ≠ Ψ' x} ⊆ T ∧ MeasurableSet T ∧ μ₂ T = 0 := by
    have h0 : μ₂ {x | Ψ x ≠ Ψ' x} = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at hae
      simpa using hae
    exact ⟨toMeasurable μ₂ {x | Ψ x ≠ Ψ' x}, subset_toMeasurable _ _, measurableSet_toMeasurable _ _,
      (measure_toMeasurable _).trans h0⟩

  set χ : G → ℂ := T.indicator (fun _ => (1 : ℂ)) with hχ
  have hχm : Measurable χ := (measurable_const.indicator hTm)
  have hχi : Integrable χ μ₂ := by
    rw [hχ, integrable_indicator_iff hTm, integrableOn_const_iff]
    right; rw [hT0]; exact ENNReal.zero_lt_top
  have hχ0 : ∫ k, χ k ∂μ₂ = 0 := by
    rw [hχ, integral_indicator hTm, setIntegral_const, Measure.real, hT0]
    simp
  obtain ⟨hχae, hχfi, hχunf⟩ := integrable_and_integral_eq_unfold μ₂ (unip p) (isClosed_unip p) μN χ hχm hχi

  have hfibχ : ∀ k : G, ∫ x : unip p, χ ((x : G) * k) ∂μN = ((μN {x : unip p | ((x : G) * k) ∈ T}).toReal : ℂ) := by
    intro k
    have hpre : MeasurableSet {x : unip p | ((x : G) * k) ∈ T} :=
      hTm.preimage ((continuous_subtype_val.mul continuous_const).measurable)
    have : (fun x : unip p => χ ((x : G) * k)) = {x : unip p | ((x : G) * k) ∈ T}.indicator (fun _ => (1 : ℂ)) := by
      funext x; rw [hχ]; by_cases hx : ((x : G) * k) ∈ T
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (by exact hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (by exact hx)]
    rw [this, integral_indicator hpre, setIntegral_const, Measure.real]
    simp
  have hzero : ∀ᵐ k ∂μD, μN {x : unip p | ((x : G) * k) ∈ T} = 0 := by
    have hre : ∫ k, ((μN {x : unip p | ((x : G) * k) ∈ T}).toReal : ℝ) ∂μD = 0 := by
      have h1 : ∫ k, (∫ x : unip p, χ ((x : G) * k) ∂μN) ∂μD = 0 := by rw [hμD]; rw [← hχunf, hχ0]
      simp_rw [hfibχ] at h1
      have h2 : ∫ k, ((μN {x : unip p | ((x : G) * k) ∈ T}).toReal : ℂ) ∂μD =
          ((∫ k, ((μN {x : unip p | ((x : G) * k) ∈ T}).toReal : ℝ) ∂μD : ℝ) : ℂ) := integral_ofReal
      rw [h2] at h1
      exact_mod_cast h1
    have hnn : 0 ≤ᵐ[μD] fun k => ((μN {x : unip p | ((x : G) * k) ∈ T}).toReal : ℝ) :=
      Filter.Eventually.of_forall fun k => ENNReal.toReal_nonneg
    have hint : Integrable (fun k => ((μN {x : unip p | ((x : G) * k) ∈ T}).toReal : ℝ)) μD := by
      have := hχfi
      simp_rw [hfibχ] at this
      rw [hμD]
      exact (this.re).congr (Filter.Eventually.of_forall fun k => by simp)
    have := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hre
    have hχae' : ∀ᵐ k ∂μD, Integrable (fun x : unip p => χ ((x : G) * k)) μN := by rw [hμD]; exact hχae
    filter_upwards [this, hχae'] with k hk hki
    have hpre : MeasurableSet {x : unip p | ((x : G) * k) ∈ T} :=
      hTm.preimage ((continuous_subtype_val.mul continuous_const).measurable)
    have hfin : μN {x : unip p | ((x : G) * k) ∈ T} ≠ ⊤ := by
      have : (fun x : unip p => χ ((x : G) * k)) = {x : unip p | ((x : G) * k) ∈ T}.indicator (fun _ => (1 : ℂ)) := by
        funext x; rw [hχ]; by_cases hx : ((x : G) * k) ∈ T
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (by exact hx)]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (by exact hx)]
      rw [this, integrable_indicator_iff hpre, integrableOn_const_iff] at hki
      exact (hki.resolve_left (by simp)).ne
    exact ((ENNReal.toReal_eq_zero_iff _).1 hk).resolve_right hfin

  have hfib : ∀ᵐ k ∂μD, ∫ x : unip p, Ψ' ((x : G) * k) ∂μN = ∫ x : unip p, Ψ ((x : G) * k) ∂μN := by
    filter_upwards [hzero] with k hk
    refine integral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) hk
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact hTsub (Ne.symm hx)

  calc ∫ k, Ψ k ∂μ₂ = ∫ k, Ψ' k ∂μ₂ := integral_congr_ae hae
    _ = ∫ k, (∫ x : unip p, Ψ' ((x : G) * k) ∂μN) ∂μD := by rw [hunf]
    _ = ∫ k, (∫ x : unip p, Ψ ((x : G) * k) ∂μN) ∂μD := integral_congr_ae hfib
    _ = ∫ k, (∫ a : F, Ψ (unipotentGL2 a * k) ∂ν) ∂μD := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        show ∫ x : unip p, Ψ ((x : G) * k) ∂μN = ∫ a : F, Ψ (unipotentGL2 a * k) ∂ν
        rw [integral_unip_eq p ν μN hμN1 (fun x : unip p => Ψ ((x : G) * k))]
        simp only [NNReal.coe_one, Complex.ofReal_one, one_mul, unipHomeo_apply_coe]

end B2Asm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual.B2Asm"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual.B2Asm"

noncomputable section

open scoped Matrix

namespace B2Asm

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat3" => (Matrix (Fin 3) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "M23" => (Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

theorem isSchwartzBruhat_zero' {Y : Type*} [TopologicalSpace Y] : IsSchwartzBruhat (fun _ : Y => (0 : ℂ)) :=
  IsSchwartzBruhat.zero

theorem isSchwartzBruhat_add {Y : Type*} [TopologicalSpace Y] (g h : Y → ℂ) (hg : IsSchwartzBruhat g)
    (hh : IsSchwartzBruhat h) : IsSchwartzBruhat (fun y => g y + h y) :=
  ⟨hg.1.add hh.1, hg.2.add hh.2⟩

theorem isSchwartzBruhat_finset_sum {Y : Type*} [TopologicalSpace Y] {ι : Type*} (s : Finset ι) (g : ι → Y → ℂ)
    (hg : ∀ i ∈ s, IsSchwartzBruhat (g i)) : IsSchwartzBruhat (fun y => ∑ i ∈ s, g i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isSchwartzBruhat_zero' (Y := Y))
  | insert a s ha ih =>
    have : (fun y => ∑ i ∈ insert a s, g i y) = fun y => g a y + ∑ i ∈ s, g i y := by
      funext y; rw [Finset.sum_insert ha]
    rw [this]
    exact isSchwartzBruhat_add _ _ (hg a (Finset.mem_insert_self a s))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem sb_comp_mul_right {N : Mat3} (hN : N.det ≠ 0) {ρ : M23 → ℂ} (hρ : IsSchwartzBruhat ρ) :
    IsSchwartzBruhat (fun Y : M23 => ρ (Y * N)) := by
  have hU : IsUnit N.det := isUnit_iff_ne_zero.2 hN
  let e : M23 ≃ₜ M23 :=
    { toFun := fun Y => Y * N
      invFun := fun Y => Y * N⁻¹
      left_inv := fun Y => by simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU]
      right_inv := fun Y => by simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  exact ⟨hρ.1.comp_continuous e.continuous, hρ.2.comp_homeomorph e⟩

theorem sb_comp_mul_left (h : G) {ρ : M23 → ℂ} (hρ : IsSchwartzBruhat ρ) :
    IsSchwartzBruhat (fun Y : M23 => ρ (((h : G) : Mat) * Y)) := by
  let e : M23 ≃ₜ M23 :=
    { toFun := fun Y => ((h : G) : Mat) * Y
      invFun := fun Y => (((h⁻¹ : G)) : Mat) * Y
      left_inv := fun Y => by
        show (((h⁻¹ : G)) : Mat) * (((h : G) : Mat) * Y) = Y
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      right_inv := fun Y => by
        show ((h : G) : Mat) * ((((h⁻¹ : G)) : Mat) * Y) = Y
        rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }
  exact ⟨hρ.1.comp_continuous e.continuous, hρ.2.comp_homeomorph e⟩

theorem continuous_transposeInvN : Continuous (fun g : G => transposeInvN (Fin 2) g) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun g : G => ((transposeInvN (Fin 2) g : G) : Mat)
    simp_rw [coe_transposeInvN]
    exact (Units.continuous_coe_inv (M := Mat)).matrix_transpose
  · show Continuous fun g : G => (((transposeInvN (Fin 2) g)⁻¹ : G) : Mat)
    simp_rw [coe_inv_transposeInvN]
    exact (Units.continuous_val (M := Mat)).matrix_transpose

def tIHomeo : G ≃ₜ G where
  toFun := fun g => transposeInvN (Fin 2) g
  invFun := fun g => transposeInvN (Fin 2) g
  left_inv := transposeInvN_transposeInvN (Fin 2)
  right_inv := transposeInvN_transposeInvN (Fin 2)
  continuous_toFun := continuous_transposeInvN p
  continuous_invFun := continuous_transposeInvN p

theorem coe_tIHomeo : (⇑(tIHomeo p) : G → G) = fun g => transposeInvN (Fin 2) g := rfl

theorem det_tI (k : G) :
    Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) k) = (Matrix.GeneralLinearGroup.det k)⁻¹ := by
  apply Units.ext
  rw [det_transposeInvN, Units.val_inv_eq_inv_val]

theorem det_w2_unit (w₂ : G) (hw₂ : ((w₂ : G) : Mat) = !![0, 1; 1, 0]) : Matrix.GeneralLinearGroup.det w₂ = -1 := by
  apply Units.ext
  rw [det_w2 p w₂ hw₂, Units.val_neg, Units.val_one]

theorem det_M_unit (g : GL (Fin 3) F) :
    Matrix.GeneralLinearGroup.det (longWeyl3 * transposeInv3 g) = -1 * (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [map_mul]
  congr 1
  · apply Units.ext; rw [det_longWeyl3, Units.val_neg, Units.val_one]
  · apply Units.ext; rw [det_transposeInv3, Units.val_inv_eq_inv_val]

theorem unipotentGL2_inv (a : F) : (unipotentGL2 a : G)⁻¹ = unipotentGL2 (-a) := by
  apply Units.ext
  show (!![1, -a; 0, 1] : Mat) = ((unipotentGL2 (-a) : G) : Mat)
  rw [unipotentGL2_coe]

theorem mC_pos (x : Fˣ) : 0 < ((modulus (x : F) : ℝ)) := by
  exact_mod_cast modulus_pos x.ne_zero

theorem mC_ne (x : Fˣ) : ((modulus (x : F) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (mC_pos p x).ne'

theorem mC_inv (x : Fˣ) : ((modulus ((x⁻¹ : Fˣ) : F) : ℝ) : ℂ) = (((modulus (x : F) : ℝ) : ℂ))⁻¹ := by
  have h : ((modulus ((x⁻¹ : Fˣ) : F) : ℝ) : ℂ) * ((modulus (x : F) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← NNReal.coe_mul, ← modulus_mul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ x.ne_zero,
      modulus_one]; simp
  exact eq_inv_of_mul_eq_one_left h

theorem mC_neg_one : ((modulus ((-1 : Fˣ) : F) : ℝ) : ℂ) = 1 := by
  have h : ((modulus ((-1 : Fˣ) : F) : ℝ) : ℂ) * ((modulus ((-1 : Fˣ) : F) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← NNReal.coe_mul, ← modulus_mul, Units.val_neg, Units.val_one, neg_one_mul, neg_neg,
      modulus_one]; simp
  have hpos : 0 ≤ ((modulus ((-1 : Fˣ) : F) : ℝ)) := NNReal.coe_nonneg _
  have hre : ((modulus ((-1 : Fˣ) : F) : ℝ)) * ((modulus ((-1 : Fˣ) : F) : ℝ)) = 1 := by exact_mod_cast h
  have : ((modulus ((-1 : Fˣ) : F) : ℝ)) = 1 := by nlinarith
  exact_mod_cast this

theorem mC_mul (x y : Fˣ) : ((modulus ((x * y : Fˣ) : F) : ℝ) : ℂ) =
    ((modulus (x : F) : ℝ) : ℂ) * ((modulus (y : F) : ℝ) : ℂ) := by
  rw [Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]

theorem cpow_half_inv (x : Fˣ) :
    ((((modulus (x : F) : ℝ) : ℂ))⁻¹) ^ (1 / 2 : ℂ) = ((((modulus (x : F) : ℝ) : ℂ)) ^ (1 / 2 : ℂ))⁻¹ := by
  apply Complex.inv_cpow
  rw [Complex.arg_ofReal_of_nonneg (NNReal.coe_nonneg _)]
  exact Real.pi_ne_zero.symm

theorem cpow_half_mul_self (x : Fˣ) :
    (((modulus (x : F) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) * (((modulus (x : F) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
      ((modulus (x : F) : ℝ) : ℂ) := by
  rw [← Complex.cpow_add _ _ (mC_ne p x)]
  norm_num

end B2Asm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual.B2Asm"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual.B2Asm"

noncomputable section

open scoped Matrix

namespace B2Asm

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat3" => (Matrix (Fin 3) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "M23" => (Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

def mC (x : Fˣ) : ℂ := ((modulus (x : F) : ℝ) : ℂ)
def sC (x : Fˣ) : ℂ := ((modulus (x : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ)

theorem mC_def (x : Fˣ) : mC p x = ((modulus (x : F) : ℝ) : ℂ) := rfl
theorem sC_def (x : Fˣ) : sC p x = ((modulus (x : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) := rfl

theorem core (μ₂ : Measure G) [μ₂.IsHaarMeasure] (η : AddChar F ℂ)
    (hη : η = psiLocal ℚ p ∨ η = (psiLocal ℚ p)⁻¹) (lam0 : Fˣ →* ℂˣ) (w₂ : G)
    (hw₂ : ((w₂ : G) : Mat) = !![0, 1; 1, 0]) (Φ : M23 → G → ℂ)
    (hΦ : ∃ (m : ℕ) (φ : Fin m → M23 → ℂ) (K : Fin m → G → ℂ),
        (∀ i, IsLocallyConstant (φ i) ∧ HasCompactSupport (φ i)) ∧
        (∀ i, IsLocallyConstant (K i) ∧ ∀ (a : F) (k : G), K i (unipotentGL2 a * k) = η a * K i k) ∧
        Φ = fun X k => ∑ i, φ i X * K i k)
    (g : GL (Fin 3) F)
    (IL IR : G → ℂ)
    (hIL : IL = fun h : G => rowFourier23 p η⁻¹
        (fun X => Φ (X * ((longWeyl3 * transposeInv3 g : GL (Fin 3) F) : Mat3)) h⁻¹) (godementArg p h)
        * ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * sC p (Matrix.GeneralLinearGroup.det h))
    (hIR : IR = fun h : G => rowFourier23 p η
        (fun X => matFourier23 p η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) h⁻¹)) (X * ((g : GL (Fin 3) F) : Mat3)))
        (godementArg p h)
        * ((lam0⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * sC p (Matrix.GeneralLinearGroup.det h))
    (hH2 : Integrable IL μ₂) (hH3 : Integrable IR μ₂) :
    ((lam0 (Matrix.GeneralLinearGroup.det (longWeyl3 * transposeInv3 g)) : ℂˣ) : ℂ)
        * mC p (Matrix.GeneralLinearGroup.det (longWeyl3 * transposeInv3 g)) * ∫ h, IL h ∂μ₂ =
      ((lam0⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mC p (Matrix.GeneralLinearGroup.det g)
        * ∫ h, IR h ∂μ₂ := by
  haveI : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨hright, hinv⟩ :=
    Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μ₂
  haveI := hright
  haveI := hinv
  obtain ⟨⟨hη0, hη1⟩, ⟨hηi0, hηi1⟩⟩ := levels p η hη

  have hΦsb : ∀ k : G, IsSchwartzBruhat (fun X : M23 => Φ X k) := by
    obtain ⟨m, φ, K, hφ, hK, hΦeq⟩ := hΦ
    intro k
    rw [hΦeq]
    exact isSchwartzBruhat_finset_sum Finset.univ (fun i X => φ i X * K i k)
      (fun i _ => ⟨(hφ i).1.mul (IsLocallyConstant.const _), (hφ i).2.mul_right⟩)
  have hΦlaw : ∀ (X : M23) (a : F) (k : G), Φ X (unipotentGL2 a * k) = η a * Φ X k := by
    obtain ⟨m, φ, K, hφ, hK, hΦeq⟩ := hΦ
    intro X a k
    rw [hΦeq]
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hK i).2 a k]; ring

  set Φ' : M23 → G → ℂ := fun X k => matFourier23 p η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) k)) X with hΦ'
  obtain ⟨hΦ'sb0, hΦ'law0⟩ := LanglandsTunnell.CubicInduction.isSchwartzBruhat_and_law_matFourier23_dualDatum p η 0 hη0 hη1
    w₂ hw₂ Φ hΦ
  have hΦ'sb : ∀ k : G, IsSchwartzBruhat (fun X : M23 => Φ' X k) := fun k => by rw [hΦ']; exact hΦ'sb0 k
  have hΦ'law : ∀ (X : M23) (a : F) (k : G), Φ' X (unipotentGL2 a * k) = η⁻¹ a * Φ' X k := fun X a k => by
    rw [hΦ']; exact hΦ'law0 X a k
  set M : GL (Fin 3) F := longWeyl3 * transposeInv3 g with hM
  set gι : GL (Fin 3) F := transposeInv3 g with hgι
  set ν : Measure F := selfDualHaarAt ℚ p with hν

  have hA : ∫ h, IL h ∂μ₂ = ∫ h, IL h⁻¹ ∂μ₂ := (integral_inv_eq_self IL μ₂).symm

  have htI : MeasurePreserving (fun h : G => transposeInvN (Fin 2) h) μ₂ μ₂ :=
    ⟨(continuous_transposeInvN p).measurable, AutomorphicForm.map_transposeInvN_eq_self_of_isHaarMeasure_fin_two p μ₂⟩
  have hemb : MeasurableEmbedding (fun h : G => transposeInvN (Fin 2) h) := by
    rw [← coe_tIHomeo]; exact (tIHomeo p).measurableEmbedding
  have hB : ∫ h, IR h ∂μ₂ = ∫ h, IR (transposeInvN (Fin 2) h⁻¹ * w₂) ∂μ₂ := by
    calc ∫ h, IR h ∂μ₂ = ∫ h, IR (h * w₂) ∂μ₂ := (integral_mul_right_eq_self _ w₂).symm
      _ = ∫ h, IR (transposeInvN (Fin 2) h * w₂) ∂μ₂ := (htI.integral_comp hemb (fun h => IR (h * w₂))).symm
      _ = ∫ h, IR (transposeInvN (Fin 2) h⁻¹ * w₂) ∂μ₂ :=
          (integral_inv_eq_self (fun h => IR (transposeInvN (Fin 2) h * w₂)) μ₂).symm

  have hILi : Integrable (fun h : G => IL h⁻¹) μ₂ := hH2.comp_inv
  have hIRi : Integrable (fun h : G => IR (transposeInvN (Fin 2) h⁻¹ * w₂)) μ₂ := by
    have h1 : Integrable (fun h : G => IR (h * w₂)) μ₂ := hH3.comp_mul_right w₂
    have h2 : Integrable (fun h : G => IR (transposeInvN (Fin 2) h * w₂)) μ₂ := (htI.integrable_comp_emb hemb).2 h1
    exact h2.comp_inv
  rw [hA, hB, unfold_unip p μ₂ _ hILi, unfold_unip p μ₂ _ hIRi, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only

  have hDl : ∀ a : F, (unipotentGL2 a * k)⁻¹ = k⁻¹ * unipotentGL2 (-a) := fun a => by
    rw [mul_inv_rev, unipotentGL2_inv]
  have hL1 : ∫ a : F, IL (unipotentGL2 a * k)⁻¹ ∂ν = ∫ a : F, IL (k⁻¹ * unipotentGL2 a) ∂ν := by
    simp_rw [hDl]
    exact integral_neg_eq_self (fun a : F => IL (k⁻¹ * unipotentGL2 a)) ν
  have hFIBl := LanglandsTunnell.CubicInduction.integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame p η 0 hη0 hη1
    lam0 Φ hΦsb hΦlaw M k⁻¹
  have hL2 : ∫ a : F, IL (k⁻¹ * unipotentGL2 a) ∂ν =
      ((lam0 (Matrix.GeneralLinearGroup.det k⁻¹) : ℂˣ) : ℂ) * sC p (Matrix.GeneralLinearGroup.det k⁻¹)
        * mC p (Matrix.GeneralLinearGroup.det k⁻¹) *
        ∫ t : F × F × F, Φ (((k⁻¹ : G) : Mat) * !![1, t.1, t.2.1; 0, 1, t.2.2] * ((M : GL (Fin 3) F) : Mat3)) k
          * η (-(t.1 + t.2.2)) ∂(jacquetHaar3 p) := by
    rw [hIL]
    simp only [sC_def, mC_def]
    rw [hFIBl, inv_inv]

  set φk : M23 → ℂ := fun Y => Φ (((k⁻¹ : G) : Mat) * Y * ((gι : GL (Fin 3) F) : Mat3)) k with hφk
  have hφk_sb : IsSchwartzBruhat φk := by
    rw [hφk]
    have h1 := sb_comp_mul_left p k⁻¹ (hΦsb k)
    have hgdet : ((gι : GL (Fin 3) F) : Mat3).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det gι).ne_zero
    simpa only [Matrix.mul_assoc] using sb_comp_mul_right p hgdet (ρ := fun Y => Φ (((k⁻¹ : G) : Mat) * Y) k) h1
  have hframe : ∀ t : F × F × F,
      Φ (((k⁻¹ : G) : Mat) * !![1, t.1, t.2.1; 0, 1, t.2.2] * ((M : GL (Fin 3) F) : Mat3)) k =
        φk !![t.2.1, t.1, 1; t.2.2, 1, 0] := by
    intro t
    rw [hφk, hM, Units.val_mul, ← frame_mul_longWeyl3 p t]
    simp only [Matrix.mul_assoc]
  have hAFF := LanglandsTunnell.CubicInduction.integral_frame23_mul_eq_integral_matFourier23_dualFrame23_mul p η hη φk hφk_sb
  have hTW : ∀ X : M23, matFourier23 p η⁻¹ φk X =
      (mC p (Matrix.GeneralLinearGroup.det k⁻¹))⁻¹ ^ 3 * (mC p (Matrix.GeneralLinearGroup.det gι))⁻¹ ^ 2 *
        matFourier23 p η⁻¹ (fun Y => Φ Y k) (((k : G) : Mat)ᵀ * X * ((g : GL (Fin 3) F) : Mat3)) := by
    intro X
    have := LanglandsTunnell.CubicInduction.matFourier23_comp_mul_mul_eq p η⁻¹ 0 hηi0 hηi1 (fun Y => Φ Y k) (hΦsb k)
      k⁻¹ gι X
    rw [hφk]
    rw [this, coe_transposeInvN_inv, hgι, transposeInvN_transposeInv3, mC_def, mC_def]

  set J : ℂ := ∫ m : F × F × F, matFourier23 p η⁻¹ (fun Y => Φ Y k)
      (((k : G) : Mat)ᵀ * !![0, 1, m.2.1; 1, m.1, m.2.2] * ((g : GL (Fin 3) F) : Mat3)) * η (m.1 + m.2.1)
      ∂(jacquetHaar3 p) with hJ
  have hLfin : ∫ a : F, IL (unipotentGL2 a * k)⁻¹ ∂ν =
      ((lam0 (Matrix.GeneralLinearGroup.det k⁻¹) : ℂˣ) : ℂ) * sC p (Matrix.GeneralLinearGroup.det k⁻¹)
        * mC p (Matrix.GeneralLinearGroup.det k⁻¹) *
        ((mC p (Matrix.GeneralLinearGroup.det k⁻¹))⁻¹ ^ 3 * (mC p (Matrix.GeneralLinearGroup.det gι))⁻¹ ^ 2 * J) := by
    rw [hL1, hL2]
    congr 1
    simp_rw [hframe]
    rw [hAFF]
    simp_rw [hTW]
    rw [hJ, ← integral_const_mul]
    congr 1
    funext m
    ring

  set h' : G := transposeInvN (Fin 2) k⁻¹ * w₂ with hh'
  have hEr : ∀ a : F, transposeInvN (Fin 2) (unipotentGL2 a * k)⁻¹ * w₂ = h' * unipotentGL2 a := by
    intro a
    rw [hDl, transposeInvN_mul, mul_assoc, transposeInvN_unipotent_mul_w2 p w₂ hw₂, ← mul_assoc, hh']
  have hFIBr := LanglandsTunnell.CubicInduction.integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame p η⁻¹ 0 hηi0 hηi1
    lam0⁻¹ Φ' hΦ'sb hΦ'law g h'
  rw [inv_inv] at hFIBr
  have hR1 : ∫ a : F, IR (transposeInvN (Fin 2) (unipotentGL2 a * k)⁻¹ * w₂) ∂ν =
      ((lam0⁻¹ (Matrix.GeneralLinearGroup.det h') : ℂˣ) : ℂ) * sC p (Matrix.GeneralLinearGroup.det h')
        * mC p (Matrix.GeneralLinearGroup.det h') *
        ∫ t : F × F × F, Φ' (((h' : G) : Mat) * !![1, t.1, t.2.1; 0, 1, t.2.2] * ((g : GL (Fin 3) F) : Mat3)) h'⁻¹
          * η⁻¹ (-(t.1 + t.2.2)) ∂(jacquetHaar3 p) := by
    simp_rw [hEr]
    rw [hIR]
    simp only [sC_def, mC_def]
    rw [← hFIBr]

  have tI_one : transposeInvN (Fin 2) (1 : G) = 1 :=
    Units.ext (by rw [coe_transposeInvN, inv_one, Units.val_one, Matrix.transpose_one])
  have tI_inv : ∀ x : G, (transposeInvN (Fin 2) x)⁻¹ = transposeInvN (Fin 2) x⁻¹ := fun x => by
    apply inv_eq_of_mul_eq_one_right
    rw [← transposeInvN_mul, mul_inv_cancel, tI_one]
  have hw2inv : w₂⁻¹ = w₂ := inv_eq_of_mul_eq_one_left (w2_mul_w2 p w₂ hw₂)
  have hk1 : w₂ * transposeInvN (Fin 2) h'⁻¹ = k := by
    rw [hh', mul_inv_rev, transposeInvN_mul, hw2inv, transposeInvN_w2 p w₂ hw₂, tI_inv, inv_inv,
      transposeInvN_transposeInvN, ← mul_assoc, w2_mul_w2 p w₂ hw₂, one_mul]
  have hcoeh' : ((h' : G) : Mat) = ((k : G) : Mat)ᵀ * !![0, 1; 1, 0] := by
    rw [hh', Units.val_mul, coe_transposeInvN_inv, hw₂]
  have hR2 : ∀ t : F × F × F,
      Φ' (((h' : G) : Mat) * !![1, t.1, t.2.1; 0, 1, t.2.2] * ((g : GL (Fin 3) F) : Mat3)) h'⁻¹ * η⁻¹ (-(t.1 + t.2.2)) =
        matFourier23 p η⁻¹ (fun Y => Φ Y k)
          (((k : G) : Mat)ᵀ * !![0, 1, t.2.2; 1, t.1, t.2.1] * ((g : GL (Fin 3) F) : Mat3)) * η (t.1 + t.2.2) := by
    intro t
    rw [hΦ']
    simp only
    rw [hk1, hcoeh', AddChar.inv_apply, neg_neg, Matrix.mul_assoc ((k : G) : Mat)ᵀ, w2_mul_frame p t]
  have hpres : MeasurePreserving
      (⇑(MeasurableEquiv.prodCongr (MeasurableEquiv.refl F) (MeasurableEquiv.prodComm : F × F ≃ᵐ F × F)))
      (jacquetHaar3 p) (jacquetHaar3 p) := by
    show MeasurePreserving _ (ν.prod (ν.prod ν)) (ν.prod (ν.prod ν))
    exact (MeasurePreserving.id ν).prod (Measure.measurePreserving_swap)
  have hswap : (∫ t : F × F × F, matFourier23 p η⁻¹ (fun Y => Φ Y k)
        (((k : G) : Mat)ᵀ * !![0, 1, t.2.2; 1, t.1, t.2.1] * ((g : GL (Fin 3) F) : Mat3)) * η (t.1 + t.2.2)
        ∂(jacquetHaar3 p)) = J := by
    rw [hJ, ← hpres.integral_comp']
    rfl
  have hRfin : ∫ a : F, IR (transposeInvN (Fin 2) (unipotentGL2 a * k)⁻¹ * w₂) ∂ν =
      ((lam0⁻¹ (Matrix.GeneralLinearGroup.det h') : ℂˣ) : ℂ) * sC p (Matrix.GeneralLinearGroup.det h')
        * mC p (Matrix.GeneralLinearGroup.det h') * J := by
    have hint : (∫ t : F × F × F, Φ' (((h' : G) : Mat) * !![1, t.1, t.2.1; 0, 1, t.2.2] * ((g : GL (Fin 3) F) : Mat3)) h'⁻¹
          * η⁻¹ (-(t.1 + t.2.2)) ∂(jacquetHaar3 p)) =
        ∫ t : F × F × F, matFourier23 p η⁻¹ (fun Y => Φ Y k)
          (((k : G) : Mat)ᵀ * !![0, 1, t.2.2; 1, t.1, t.2.1] * ((g : GL (Fin 3) F) : Mat3)) * η (t.1 + t.2.2)
          ∂(jacquetHaar3 p) := integral_congr_ae (Filter.Eventually.of_forall hR2)
    rw [hR1, hint, hswap]

  rw [show (selfDualHaarAt ℚ p : Measure F) = ν from rfl] at *
  rw [hLfin, hRfin]

  have hdk : Matrix.GeneralLinearGroup.det k⁻¹ = (Matrix.GeneralLinearGroup.det k)⁻¹ := map_inv _ _
  have hdh' : Matrix.GeneralLinearGroup.det h' = Matrix.GeneralLinearGroup.det k * (-1) := by
    rw [hh', map_mul, det_tI, hdk, inv_inv, det_w2_unit p w₂ hw₂]
  have hdM : Matrix.GeneralLinearGroup.det M = -1 * (Matrix.GeneralLinearGroup.det g)⁻¹ := by rw [hM]; exact det_M_unit p g
  have hdgι : Matrix.GeneralLinearGroup.det gι = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
    apply Units.ext; rw [hgι, det_transposeInv3, Units.val_inv_eq_inv_val]
  rw [hdk, hdh', hdgι]
  rw [show Matrix.GeneralLinearGroup.det (longWeyl3 * transposeInv3 g) = Matrix.GeneralLinearGroup.det M from by rw [hM], hdM]

  set d := Matrix.GeneralLinearGroup.det k with hd
  set e := Matrix.GeneralLinearGroup.det g with he
  have hL1 : ((lam0 (-1) : ℂˣ) : ℂ) * ((lam0 (-1) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul]
    simp
  have hx : sC p d * sC p d = mC p d := by rw [sC_def, mC_def]; exact cpow_half_mul_self p d
  have hxne : mC p d ≠ 0 := mC_ne p d
  have hyne : sC p d ≠ 0 := by
    intro h0; apply hxne; rw [← hx, h0, zero_mul]
  have hzne : mC p e ≠ 0 := mC_ne p e

  have e1 : mC p (-1 * e⁻¹) = (mC p e)⁻¹ := by rw [mC_def, mC_mul, mC_neg_one, one_mul, mC_inv]; rfl
  have e2 : sC p d⁻¹ = (sC p d)⁻¹ := by
    rw [sC_def, sC_def]
    have := mC_inv p d
    rw [this]
    exact cpow_half_inv p d
  have e3 : mC p d⁻¹ = (mC p d)⁻¹ := by rw [mC_def, mC_inv]; rfl
  have e4 : mC p e⁻¹ = (mC p e)⁻¹ := by rw [mC_def, mC_inv]; rfl
  have e5 : sC p (d * -1) = sC p d := by
    rw [sC_def, sC_def]
    have := mC_mul p d (-1)
    rw [mC_neg_one, mul_one] at this
    rw [this]
  have e6 : mC p (d * -1) = mC p d := by rw [mC_def, mC_mul, mC_neg_one, mul_one]; rfl
  have e7 : ((lam0 (-1 * e⁻¹) : ℂˣ) : ℂ) = ((lam0 (-1) : ℂˣ) : ℂ) * (((lam0 e : ℂˣ) : ℂ))⁻¹ := by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  have e8 : ((lam0 d⁻¹ : ℂˣ) : ℂ) = (((lam0 d : ℂˣ) : ℂ))⁻¹ := by rw [map_inv, Units.val_inv_eq_inv_val]
  have e9 : ((lam0⁻¹ e : ℂˣ) : ℂ) = (((lam0 e : ℂˣ) : ℂ))⁻¹ := by rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have e10 : ((lam0⁻¹ (d * -1) : ℂˣ) : ℂ) = (((lam0 d : ℂˣ) : ℂ))⁻¹ * (((lam0 (-1) : ℂˣ) : ℂ))⁻¹ := by
    rw [MonoidHom.inv_apply, map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  have hL1' : (((lam0 (-1) : ℂˣ) : ℂ))⁻¹ = ((lam0 (-1) : ℂˣ) : ℂ) := inv_eq_of_mul_eq_one_left hL1
  rw [hL1', ← hx]
  have hLne : ((lam0 d : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hLgne : ((lam0 e : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hL1ne : ((lam0 (-1) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

end B2Asm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual.B2Asm"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual.B2Asm"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

open B2Asm in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (η : AddChar (p.adicCompletion ℚ) ℂ),
      (η = psiLocal ℚ p ∨ η = (psiLocal ℚ p)⁻¹) →
    ∀ (lam0 : (p.adicCompletion ℚ)ˣ →* ℂˣ)
      (w₂ : GL (Fin 2) (p.adicCompletion ℚ)),
      ((w₂ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) →
    ∀ (Φ : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),

      (∃ (m : ℕ) (φ : Fin m → Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → ℂ)
          (K : Fin m → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
          (∀ i, IsLocallyConstant (φ i) ∧ HasCompactSupport (φ i)) ∧
          (∀ i, IsLocallyConstant (K i) ∧
            ∀ (a : p.adicCompletion ℚ) (k : GL (Fin 2) (p.adicCompletion ℚ)), K i (unipotentGL2 a * k) = η a * K i k) ∧
          Φ = fun X k => ∑ i, φ i X * K i k) →
    ∀ (g : LocalGL3 p),

      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        rowFourier23 p η⁻¹
            (fun X => Φ (X * ((longWeyl3 * transposeInv3 g : LocalGL3 p) :
              Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹) (godementArg p h)
          * ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ)) μ₂ →

      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        rowFourier23 p η
            (fun X => matFourier23 p η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) h⁻¹))
              (X * ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))))
            (godementArg p h)
          * ((lam0⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ)) μ₂ →
      dualWhittakerFn3 (godementWhittaker3 p η μ₂ lam0 Φ) g =
        godementWhittaker3 p η⁻¹ μ₂ lam0⁻¹
          (fun X k => matFourier23 p η⁻¹ (fun Y => Φ Y (w₂ * transposeInvN (Fin 2) k)) X) g := by
  intro μ₂ _ η hη lam0 w₂ hw₂ Φ hΦ g hH2 hH3
  rw [dualWhittakerFn3_apply, godementWhittaker3_apply, godementWhittaker3_apply]
  simp only [inv_inv]
  exact core p μ₂ η hη lam0 w₂ hw₂ Φ hΦ g _ _ rfl rfl hH2 hH3

end S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_dualWhittakerFn3_godementWhittaker3_eq_godementWhittaker3_matFourier23_dual (solution)
