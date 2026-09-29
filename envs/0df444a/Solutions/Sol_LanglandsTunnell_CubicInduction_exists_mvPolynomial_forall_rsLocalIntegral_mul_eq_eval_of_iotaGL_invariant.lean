-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/9a4721b4-3307-5da1-871b-79d2bbf2ddad

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Theorems.Thm_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral
import Theorems.Thm_Polynomial_exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_polynomial_sum_coeff_smul_rightTranslate_pow_mem_span_radical_of_admissible
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_torus_eq_zero_of_mem_span_radical_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

open LanglandsTunnell.CubicInduction

noncomputable section

namespace SlCR

open scoped ENNReal NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev Fv : Type := v.adicCompletion ℚ

abbrev G2 : Type := GL (Fin 2) (v.adicCompletion ℚ)

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (Fv v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → Fv v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (Fv v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_G2 : SecondCountableTopology (G2 v) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

abbrev unip : Subgroup (G2 v) := (unipotentGL2Hom (R := Fv v)).range

theorem unip_eq_unipotentGL2 (n : unip v) : (n : G2 v) = unipotentGL2 (((n : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) 0 1) := by
  obtain ⟨z, hz⟩ := n.2
  rw [← hz]
  change (unipotentGL2 z.toAdd : G2 v) = unipotentGL2 (((unipotentGL2 z.toAdd : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) 0 1)
  have h01 : (((unipotentGL2 z.toAdd : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) 0 1) = z.toAdd := by simp [unipotentGL2_coe]
  rw [h01]

theorem unip_comm (m n : unip v) : m * n = n * m := by
  refine Subtype.ext ?_
  change (m : G2 v) * (n : G2 v) = (n : G2 v) * (m : G2 v)
  rw [unip_eq_unipotentGL2 v m, unip_eq_unipotentGL2 v n, ← unipotentGL2_add, ← unipotentGL2_add, add_comm]

theorem unipotent_eq (x : Fv v) : UnramifiedWhittaker.unipotent x = unipotentGL2 x := Units.ext rfl

theorem isMulRightInvariant_unip {_i : MeasurableSpace (unip v)} (μN : Measure (unip v)) [μN.IsMulLeftInvariant] :
    μN.IsMulRightInvariant := by
  constructor
  intro g
  have : (fun x : unip v => x * g) = fun x => g * x := funext fun x => unip_comm v x g
  rw [this]
  exact map_mul_left_eq_self μN g

theorem det_unipotentGL2 (x : Fv v) : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G2 v) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem v_det_le_one_of_entries {M : Matrix (Fin 2) (Fin 2) (Fv v)} (h : ∀ i j, Valued.v (M i j) ≤ 1) :
    Valued.v M.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul]
  · exact (mul_le_mul' (h 0 0) (h 1 1)).trans_eq (one_mul 1)
  · exact (mul_le_mul' (h 0 1) (h 1 0)).trans_eq (one_mul 1)

theorem v_det_eq_one_of_mem {k : G2 v} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    Valued.v (((Matrix.GeneralLinearGroup.det k : (Fv v)ˣ)) : Fv v) = 1 := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk
  obtain ⟨⟨h1, -, -⟩, ⟨h2, -, -⟩⟩ := hk
  have h1' : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (Fv v)) i j) ≤ 1 := fun i j =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp (h1 i j)
  have h2' : ∀ i j, Valued.v (((k⁻¹ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) i j) ≤ 1 := fun i j =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp (h2 i j)
  have hd : Valued.v (((Matrix.GeneralLinearGroup.det k : (Fv v)ˣ)) : Fv v) ≤ 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; exact v_det_le_one_of_entries v h1'
  have hdi : Valued.v (((Matrix.GeneralLinearGroup.det k⁻¹ : (Fv v)ˣ)) : Fv v) ≤ 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; exact v_det_le_one_of_entries v h2'
  have hprod : Valued.v (((Matrix.GeneralLinearGroup.det k : (Fv v)ˣ)) : Fv v) *
      Valued.v (((Matrix.GeneralLinearGroup.det k⁻¹ : (Fv v)ˣ)) : Fv v) = 1 := by
    rw [← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, map_one]
  refine le_antisymm hd ?_
  by_contra h
  push Not at h
  have : Valued.v (((Matrix.GeneralLinearGroup.det k : (Fv v)ˣ)) : Fv v) *
      Valued.v (((Matrix.GeneralLinearGroup.det k⁻¹ : (Fv v)ˣ)) : Fv v) < 1 :=
    lt_of_le_of_lt (mul_le_mul_right hdi _) (by rwa [mul_one])
  exact absurd hprod (ne_of_lt this)

end SlCR
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant.SlCR"

namespace SlCR

open WithZero

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev mat (g : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v) := (g : Matrix (Fin 2) (Fin 2) (Fv v))

theorem mem_K {k : G2 v} (h1 : ∀ i j, Valued.v (mat v k i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (mat v k⁻¹ i j) ≤ 1) : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  rw [AdelicDock.mem_localLevelOne_iff]
  have hsub : ∀ x : Fv v, Valued.v x ≤ 1 → Valued.v (x - 1) ≤ 1 := fun x hx =>
    (Valuation.map_sub _ _ _).trans (max_le hx (le_of_eq (Valuation.map_one _)))
  refine ⟨⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (h1 i j), ?_, ?_⟩,
    ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (h2 i j), ?_, ?_⟩⟩
  · rw [AdelicLevel.idealBound_top]; exact h1 1 0
  · rw [AdelicLevel.idealBound_top]; exact hsub _ (h1 1 1)
  · rw [AdelicLevel.idealBound_top]; exact h2 1 0
  · rw [AdelicLevel.idealBound_top]; exact hsub _ (h2 1 1)

theorem v_zero_le : Valued.v (0 : Fv v) ≤ 1 := by rw [map_zero]; exact zero_le'
theorem v_one_le : Valued.v (1 : Fv v) ≤ 1 := by rw [map_one]

theorem unipotentGL2_mem {x : Fv v} (hx : Valued.v x ≤ 1) : (unipotentGL2 x : G2 v) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  have hx' : Valued.v (-x) ≤ 1 := by rwa [Valuation.map_neg]
  refine mem_K v (fun i j => ?_) (fun i j => ?_)
  · rw [show mat v (unipotentGL2 x) = !![1, x; 0, 1] from rfl]
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact v_one_le v | exact v_zero_le v | exact hx
  · rw [show mat v (unipotentGL2 x)⁻¹ = !![1, -x; 0, 1] from rfl]
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact v_one_le v | exact v_zero_le v | exact hx'

def dU (α β : (Fv v)ˣ) : GL (Fin 2) (Fv v) :=
  ⟨!![(α : Fv v), 0; 0, (β : Fv v)], !![((α⁻¹ : (Fv v)ˣ) : Fv v), 0; 0, ((β⁻¹ : (Fv v)ˣ) : Fv v)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_dU (α β : (Fv v)ˣ) :
    ((dU v α β : GL (Fin 2) (Fv v)) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![(α : Fv v), 0; 0, (β : Fv v)] := rfl

theorem dU_mul (α β γ δ : (Fv v)ˣ) : dU v α β * dU v γ δ = dU v (α * γ) (β * δ) := by
  apply Units.ext
  rw [Units.val_mul, coe_dU, coe_dU, coe_dU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def sHom : (Fv v)ˣ →* GL (Fin 2) (Fv v) where
  toFun α := dU v α α
  map_one' := by
    apply Units.ext
    rw [coe_dU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' α γ := (dU_mul v α α γ γ).symm

theorem scalarPi_eq (π : Fv v) (hπ : π ≠ 0) : scalarPi π hπ = sHom v (Units.mk0 π hπ) := by
  apply Units.ext
  show (!![π, 0; 0, π] : Matrix (Fin 2) (Fin 2) (Fv v)) = ((dU v (Units.mk0 π hπ) (Units.mk0 π hπ) : GL (Fin 2) (Fv v)) : Matrix _ _ _)
  rw [coe_dU]
  rfl

theorem scalarPi_zpow (π : Fv v) (hπ : π ≠ 0) (n : ℤ) :
    scalarPi π hπ ^ n = dU v (Units.mk0 π hπ ^ n) (Units.mk0 π hπ ^ n) := by
  rw [scalarPi_eq, ← map_zpow]
  rfl

theorem diagUnitGL2_eq (w : (Fv v)ˣ) : diagUnitGL2 w = dU v w 1 := by
  apply Units.ext
  rw [coe_diagUnitGL2, coe_dU, Units.val_one]

theorem torus_eq (π : Fv v) (hπ : π ≠ 0) (n₁ n₂ : ℤ) :
    scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁) =
      dU v (Units.mk0 π hπ ^ n₂ * Units.mk0 π hπ ^ n₁) (Units.mk0 π hπ ^ n₂) := by
  rw [scalarPi_zpow, diagUnitGL2_eq, dU_mul, mul_one]

theorem iotaGL_dU_mul_upperUnipotent3 (α β : (Fv v)ˣ) (x y z : Fv v) :
    iotaGL (dU v α β) * upperUnipotent3 x y z =
      upperUnipotent3 ((α : Fv v) * ((β⁻¹ : (Fv v)ˣ) : Fv v) * x) ((β : Fv v) * y) ((α : Fv v) * z) *
        iotaGL (dU v α β) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_iotaGL, coe_dU, upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  have hβ : ((β : (Fv v)ˣ) : Fv v) ≠ 0 := Units.ne_zero β
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, embedMat2]
  first | (field_simp; done) | (field_simp; ring)

theorem scalarPi_comm (π : Fv v) (hπ : π ≠ 0) (g : G2 v) : g * scalarPi π hπ = scalarPi π hπ * g := by
  apply Units.ext
  show (g : Matrix (Fin 2) (Fin 2) (Fv v)) * !![π, 0; 0, π] = !![π, 0; 0, π] * (g : Matrix (Fin 2) (Fin 2) (Fv v))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem scalarPi_pow_comm (π : Fv v) (hπ : π ≠ 0) (g : G2 v) (j : ℕ) : g * scalarPi π hπ ^ j = scalarPi π hπ ^ j * g := by
  have h : Commute (scalarPi π hπ) g := (scalarPi_comm v π hπ g).symm
  exact (h.pow_left j).eq.symm

theorem diagZ_mul_scalarPi_zpow (π : Fv v) (hπ : π ≠ 0) (m k : ℤ) :
    diagZ π hπ m * scalarPi π hπ ^ k = scalarPi π hπ ^ k * diagUnitGL2 (Units.mk0 π hπ ^ m) := by
  rw [scalarPi_zpow, diagUnitGL2_eq, dU_mul, mul_one]
  have : diagZ π hπ m = dU v (Units.mk0 π hπ ^ m) 1 := by
    apply Units.ext
    show (!![π ^ m, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (Fv v)) = _
    rw [coe_dU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Units.val_zpow_eq_zpow_val]
  rw [this, dU_mul, one_mul, mul_comm]

theorem continuous_root23 : Continuous fun y : Fv v => (upperUnipotent3 0 y 0 : LocalGL3 v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Function.comp_def, upperUnipotent3_coe]
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop
  · have : ∀ y : Fv v, (((upperUnipotent3 0 y 0 : LocalGL3 v)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (Fv v)) =
        !![1, -0, 0 * y - 0; 0, 1, -y; 0, 0, 1] := fun y => rfl
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Function.comp_def, this]
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop

theorem exists_forall_root23_mem {S : Subgroup (LocalGL3 v)} (hS : IsOpen (S : Set (LocalGL3 v))) :
    ∃ e : ℕ, ∀ y : Fv v, Valued.v y ≤ WithZero.exp (-(e : ℤ)) → (upperUnipotent3 0 y 0 : LocalGL3 v) ∈ S := by
  have h0 : (upperUnipotent3 0 (0 : Fv v) 0 : LocalGL3 v) = 1 := by
    apply Units.ext; rw [upperUnipotent3_coe, Units.val_one]; ext i j; fin_cases i <;> fin_cases j <;> simp
  have h1 : (fun y : Fv v => (upperUnipotent3 0 y 0 : LocalGL3 v)) ⁻¹' (S : Set (LocalGL3 v)) ∈ nhds (0 : Fv v) :=
    (continuous_root23 v).continuousAt.preimage_mem_nhds (by rw [h0]; exact hS.mem_nhds S.one_mem)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 h1
  have hE : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ 0 :=
    (map_ne_zero MonoidWithZeroHom.ValueGroup₀.embedding).2 γ.ne_zero
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.val)).toNat, fun z hz => hγ ?_⟩
  rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  exact hz.trans_lt ((WithZero.exp_lt_exp.2 (by omega)).trans_eq (WithZero.exp_log hE))

theorem coeff_sum_monomial (d : ℕ) (c : ℕ → ℂ) (m : ℕ) :
    (∑ n ∈ Finset.range (d + 1), Polynomial.monomial n (c n)).coeff m = if m < d + 1 then c m else 0 := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (d + 1)) m c]
  simp only [Finset.mem_range]

theorem reverse_recurrence (C : Polynomial ℂ) (hC : C ≠ 0) :
    ∃ D : Polynomial ℂ, D.eval 0 ≠ 0 ∧ D.natDegree ≤ C.natDegree ∧ ∀ (b : ℤ → ℂ) (N₀ : ℤ),
      (∀ n : ℤ, N₀ ≤ n → ∑ i ∈ Finset.range (C.natDegree + 1), C.coeff i * b (n + i) = 0) →
      ∀ m : ℤ, N₀ + C.natDegree ≤ m → ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * b (m - i) = 0 := by
  set d := C.natDegree with hd
  set D : Polynomial ℂ := ∑ n ∈ Finset.range (d + 1), Polynomial.monomial n (C.coeff (d - n)) with hD
  have hcoeff : ∀ i, D.coeff i = if i < d + 1 then C.coeff (d - i) else 0 := fun i => by
    rw [hD, coeff_sum_monomial]
  have hdeg : D.natDegree ≤ d := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi; rw [hcoeff, if_neg (by omega)]
  refine ⟨D, ?_, hdeg, fun b N₀ h m hm => ?_⟩
  · rw [← Polynomial.coeff_zero_eq_eval_zero, hcoeff, if_pos (by omega), Nat.sub_zero]
    exact Polynomial.leadingCoeff_ne_zero.mpr hC
  ·
    have e1 : ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * b (m - i) =
        ∑ i ∈ Finset.range (d + 1), D.coeff i * b (m - i) := by
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
      rw [Finset.mem_range, not_lt] at hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
    rw [e1]
    have e2 : ∑ i ∈ Finset.range (d + 1), D.coeff i * b (m - i) =
        ∑ j ∈ Finset.range (d + 1), C.coeff j * b ((m - d) + j) := by
      rw [← Finset.sum_range_reflect (fun j => C.coeff j * b ((m - d) + j)) (d + 1)]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [hcoeff, if_pos hi, show d + 1 - 1 - i = d - i by omega]
      congr 1
      push_cast [Nat.cast_sub (show i ≤ d by omega)]
      ring_nf
    rw [e2]
    exact h (m - d) (by omega)

end SlCR
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant.SlCR"

namespace SlCR

variable (v : HeightOneSpectrum (𝓞 ℚ))

def dHom1 : (Fv v)ˣ →* GL (Fin 2) (Fv v) where
  toFun α := dU v α 1
  map_one' := by
    apply Units.ext
    rw [coe_dU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' α γ := by show dU v (α * γ) 1 = dU v α 1 * dU v γ 1; rw [dU_mul, mul_one]

theorem diagUnitGL2_zpow_mul_pow (w : (Fv v)ˣ) (n : ℤ) (i : ℕ) :
    diagUnitGL2 (w ^ n) * diagUnitGL2 w ^ i = diagUnitGL2 (w ^ (n + i)) := by
  rw [diagUnitGL2_eq, diagUnitGL2_eq, diagUnitGL2_eq, show dU v w 1 = dHom1 v w from rfl, ← map_pow,
    show dHom1 v (w ^ i) = dU v (w ^ i) 1 from rfl, dU_mul, mul_one, ← zpow_natCast, ← zpow_add]

theorem v_zpow {ϖ : Fv v} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (a : ℤ) :
    Valued.v (ϖ ^ a) = WithZero.exp (-a) := by
  rw [map_zpow₀, hϖ]
  have hne : (WithZero.exp (-1 : ℤ)) ^ a ≠ 0 := zpow_ne_zero a WithZero.exp_ne_zero
  rw [← WithZero.exp_log hne, WithZero.log_zpow, WithZero.log_exp, smul_eq_mul, mul_neg_one]

theorem coe_ratio {ϖ : Fv v} (hπ : ϖ ≠ 0) (n₁ n₂ : ℤ) :
    (((Units.mk0 ϖ hπ ^ n₂ * Units.mk0 ϖ hπ ^ n₁ : (Fv v)ˣ)) : Fv v) *
        (((Units.mk0 ϖ hπ ^ n₂)⁻¹ : (Fv v)ˣ) : Fv v) = ϖ ^ n₁ := by
  rw [← Units.val_mul, mul_comm (Units.mk0 ϖ hπ ^ n₂), mul_assoc, mul_inv_cancel, mul_one,
    Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem coe_pow {ϖ : Fv v} (hπ : ϖ ≠ 0) (n : ℤ) : (((Units.mk0 ϖ hπ ^ n : (Fv v)ˣ)) : Fv v) = ϖ ^ n := by
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem torus_mul_scalarPi_pow (π : Fv v) (hπ : π ≠ 0) (n₂ n₁ : ℤ) (j : ℕ) :
    scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁) * scalarPi π hπ ^ j =
      scalarPi π hπ ^ (n₂ + (j : ℤ)) * diagUnitGL2 (Units.mk0 π hπ ^ n₁) := by
  rw [mul_assoc, scalarPi_pow_comm v π hπ, ← mul_assoc, ← zpow_natCast, ← zpow_add]

theorem mem_gl3CyclicSubspace_self (W : LocalGL3 v → ℂ) : W ∈ gl3CyclicSubspace W := by
  refine Submodule.subset_span ⟨1, ?_⟩
  funext g
  simp [gl3AmbientRightTranslate_apply]

theorem torus_array (θ' : AddChar (Fv v) ℂ)
    (hθ'1 : ∃ y : Fv v, Valued.v y ≤ WithZero.exp (1 : ℤ) ∧ θ' y ≠ 1)
    (π : Fv v) (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ))
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn θ' W)
    (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, W (g * iotaGL k) = W g)
    (Uv : Subgroup (LocalGL3 v)) (hUo : IsOpen (Uv : Set (LocalGL3 v))) (hUv : ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (C₁ C₂ : Polynomial ℂ) (hC₁ : C₁ ≠ 0) (hC₂ : C₂ ≠ 0) (N₁ N₂ : ℤ)
    (hN₁ : ∀ n₁ n₂ : ℤ, N₁ ≤ n₁ →
      (∑ i ∈ Finset.range (C₁.natDegree + 1), C₁.coeff i • fun g : LocalGL3 v => W (g * iotaGL (diagUnitGL2 (Units.mk0 π hπ)) ^ i))
        (iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁))) = 0)
    (hN₂ : ∀ n₁ n₂ : ℤ, N₂ ≤ n₂ →
      (∑ i ∈ Finset.range (C₂.natDegree + 1), C₂.coeff i • fun g : LocalGL3 v => W (g * iotaGL (scalarPi π hπ) ^ i))
        (iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁))) = 0) :
    ∃ (e : ℕ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n₁ n₂ : ℤ, (n₁ < 0 ∨ n₂ < -(e : ℤ)) →
        W (iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁))) = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l *
            W (iotaGL (scalarPi π hπ ^ ((m₂ : ℤ) - (l : ℤ) - (e : ℤ)) * diagUnitGL2 (Units.mk0 π hπ ^ ((m₁ : ℤ) - (i : ℤ))))) = 0) := by
  obtain ⟨y₀, hy₀v, hy₀⟩ := hθ'1
  obtain ⟨e, he⟩ := exists_forall_root23_mem v hUo

  have hvy : ∀ (n c : ℤ), n + 1 ≤ c → Valued.v (y₀ * π ^ (-n)) ≤ WithZero.exp c := by
    intro n c hnc
    rw [map_mul, v_zpow v hϖ, neg_neg]
    calc Valued.v y₀ * WithZero.exp n ≤ WithZero.exp 1 * WithZero.exp n := mul_le_mul' hy₀v le_rfl
      _ = WithZero.exp (1 + n) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp c := WithZero.exp_le_exp.mpr (by omega)
  have hπy : ∀ n : ℤ, π ^ n * (y₀ * π ^ (-n)) = y₀ := by
    intro n
    rw [mul_comm, mul_assoc, ← zpow_add₀ hπ, neg_add_cancel, zpow_zero, mul_one]

  have hS1 : ∀ n₁ n₂ : ℤ, n₁ < 0 → W (iotaGL ((scalarPi π hπ) ^ n₂ * diagUnitGL2 ((Units.mk0 π hπ) ^ n₁))) = 0 := by
    intro n₁ n₂ hn
    have hxv : Valued.v (y₀ * π ^ (-n₁)) ≤ 1 := by
      have := hvy n₁ 0 (by omega); rwa [WithZero.exp_zero] at this
    have hk := hK (unipotentGL2 (y₀ * π ^ (-n₁))) (unipotentGL2_mem v hxv)
      (iotaGL ((scalarPi π hπ) ^ n₂ * diagUnitGL2 ((Units.mk0 π hπ) ^ n₁)))
    rw [iotaGL_unipotentGL2, torus_eq, iotaGL_dU_mul_upperUnipotent3, hW, coe_ratio v hπ, mul_zero,
      add_zero, hπy] at hk
    rw [torus_eq]
    have : (θ' y₀ - 1) * W (iotaGL (dU v ((Units.mk0 π hπ) ^ n₂ * (Units.mk0 π hπ) ^ n₁) ((Units.mk0 π hπ) ^ n₂))) = 0 := by
      rw [sub_mul, one_mul, hk, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hy₀)

  have hS2 : ∀ n₁ n₂ : ℤ, n₂ < -(e : ℤ) → W (iotaGL ((scalarPi π hπ) ^ n₂ * diagUnitGL2 ((Units.mk0 π hπ) ^ n₁))) = 0 := by
    intro n₁ n₂ hn
    have hyv : Valued.v (y₀ * π ^ (-n₂)) ≤ WithZero.exp (-(e : ℤ)) := hvy n₂ _ (by omega)
    have hk := hUv _ (he _ hyv) (iotaGL ((scalarPi π hπ) ^ n₂ * diagUnitGL2 ((Units.mk0 π hπ) ^ n₁)))
    rw [torus_eq, iotaGL_dU_mul_upperUnipotent3, hW, coe_pow v hπ, mul_zero, zero_add, hπy] at hk
    rw [torus_eq]
    have : (θ' y₀ - 1) * W (iotaGL (dU v ((Units.mk0 π hπ) ^ n₂ * (Units.mk0 π hπ) ^ n₁) ((Units.mk0 π hπ) ^ n₂))) = 0 := by
      rw [sub_mul, one_mul, hk, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hy₀)

  have hR1 : ∀ n₂ n₁ : ℤ, N₁ ≤ n₁ → ∑ i ∈ Finset.range (C₁.natDegree + 1),
      C₁.coeff i * W (iotaGL ((scalarPi π hπ) ^ n₂ * diagUnitGL2 ((Units.mk0 π hπ) ^ (n₁ + i)))) = 0 := by
    intro n₂ n₁ hn
    have h := hN₁ n₁ n₂ hn
    rw [Finset.sum_apply] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_pow, ← map_mul, mul_assoc, diagUnitGL2_zpow_mul_pow]
  have hR2 : ∀ n₁ n₂ : ℤ, N₂ ≤ n₂ → ∑ j ∈ Finset.range (C₂.natDegree + 1),
      C₂.coeff j * W (iotaGL ((scalarPi π hπ) ^ (n₂ + j) * diagUnitGL2 ((Units.mk0 π hπ) ^ n₁))) = 0 := by
    intro n₁ n₂ hn
    have h := hN₂ n₁ n₂ hn
    rw [Finset.sum_apply] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_pow, ← map_mul, torus_mul_scalarPi_pow v π hπ n₂ n₁ j]

  obtain ⟨D₁, hD₁0, hD₁deg, hD₁⟩ := reverse_recurrence C₁ hC₁
  obtain ⟨D₂, hD₂0, hD₂deg, hD₂⟩ := reverse_recurrence C₂ hC₂
  refine ⟨e, D₁, D₂, (max (N₁ + C₁.natDegree) (N₂ + C₂.natDegree + e)).toNat, hD₁0, hD₂0, ?_, ?_⟩
  · intro n₁ n₂ h
    exact h.elim (hS1 n₁ n₂) (hS2 n₁ n₂)
  · intro m₁ m₂ hM
    have hMle : max (N₁ + C₁.natDegree) (N₂ + C₂.natDegree + e) ≤
        ((max (N₁ + C₁.natDegree) (N₂ + C₂.natDegree + e)).toNat : ℤ) := Int.self_le_toNat _
    rcases hM with h1 | h2
    ·
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l _ => ?_
      have hrel := hD₁ (fun n => W (iotaGL ((scalarPi π hπ) ^ ((m₂ : ℤ) - (l : ℤ) - (e : ℤ)) * diagUnitGL2 ((Units.mk0 π hπ) ^ n)))) N₁
        (fun n hn => hR1 _ n hn) m₁ (by have := le_max_left (N₁ + C₁.natDegree) (N₂ + C₂.natDegree + e); omega)
      have e1 : ∀ i ∈ Finset.range (D₁.natDegree + 1),
          D₁.coeff i * D₂.coeff l * W (iotaGL ((scalarPi π hπ) ^ ((m₂ : ℤ) - (l : ℤ) - (e : ℤ)) * diagUnitGL2 ((Units.mk0 π hπ) ^ ((m₁ : ℤ) - (i : ℤ))))) =
          D₂.coeff l * (D₁.coeff i * W (iotaGL ((scalarPi π hπ) ^ ((m₂ : ℤ) - (l : ℤ) - (e : ℤ)) * diagUnitGL2 ((Units.mk0 π hπ) ^ ((m₁ : ℤ) - (i : ℤ)))))) :=
        fun i _ => by rw [mul_comm (D₁.coeff i) (D₂.coeff l), mul_assoc]
      rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, hrel, mul_zero]
    · refine Finset.sum_eq_zero fun i _ => ?_
      have hrel := hD₂ (fun n => W (iotaGL ((scalarPi π hπ) ^ n * diagUnitGL2 ((Units.mk0 π hπ) ^ ((m₁ : ℤ) - (i : ℤ)))))) N₂
        (fun n hn => hR2 _ n hn) ((m₂ : ℤ) - (e : ℤ))
        (by have := le_max_right (N₁ + C₁.natDegree) (N₂ + C₂.natDegree + e); omega)
      have e1 : ∀ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * W (iotaGL ((scalarPi π hπ) ^ ((m₂ : ℤ) - (l : ℤ) - (e : ℤ)) * diagUnitGL2 ((Units.mk0 π hπ) ^ ((m₁ : ℤ) - (i : ℤ))))) =
          D₁.coeff i * (D₂.coeff l * W (iotaGL ((scalarPi π hπ) ^ ((m₂ : ℤ) - (e : ℤ) - (l : ℤ)) * diagUnitGL2 ((Units.mk0 π hπ) ^ ((m₁ : ℤ) - (i : ℤ)))))) :=
        fun l _ => by rw [show (m₂ : ℤ) - (l : ℤ) - (e : ℤ) = (m₂ : ℤ) - (e : ℤ) - (l : ℤ) by ring, mul_assoc]
      rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, hrel, mul_zero]

end SlCR
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant.SlCR"

namespace SlCR

open scoped NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

def hs (a₁ a₂ : ℂ) (m : ℕ) : ℂ := ∑ i ∈ Finset.range (m + 1), a₁ ^ i * a₂ ^ (m - i)

theorem hs_zero (a₁ a₂ : ℂ) : hs a₁ a₂ 0 = 1 := by simp [hs]

theorem hs_succ (a₁ a₂ : ℂ) (m : ℕ) : hs a₁ a₂ (m + 1) = a₂ * hs a₁ a₂ m + a₁ ^ (m + 1) := by
  unfold hs
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [show m + 1 - i = (m - i) + 1 by omega, pow_succ]
  ring

theorem hs_rec (a₁ a₂ : ℂ) (m : ℕ) : hs a₁ a₂ (m + 2) = (a₁ + a₂) * hs a₁ a₂ (m + 1) - a₁ * a₂ * hs a₁ a₂ m := by
  rw [show m + 2 = (m + 1) + 1 from rfl, hs_succ, hs_succ]; ring

theorem torusFactor_eq (N : ℂ) (hN : N ≠ 0) (a₁ a₂ : ℂ) (m : ℕ) :
    torusFactor N (a₁ + a₂) (a₁ * a₂ / N) (m : ℤ) = N⁻¹ ^ m * hs a₁ a₂ m := by
  rw [torusFactor, if_pos (Int.natCast_nonneg m), Int.toNat_natCast]
  suffices h : ∀ m : ℕ, heckeRecursionSeq N (a₁ + a₂) (a₁ * a₂ / N) m = N⁻¹ ^ m * hs a₁ a₂ m ∧
      heckeRecursionSeq N (a₁ + a₂) (a₁ * a₂ / N) (m + 1) = N⁻¹ ^ (m + 1) * hs a₁ a₂ (m + 1) from (h m).1
  intro m
  induction m with
  | zero =>
    refine ⟨by simp [heckeRecursionSeq, hs_zero], ?_⟩
    show (a₁ + a₂) / N = N⁻¹ ^ (0 + 1) * hs a₁ a₂ (0 + 1)
    rw [zero_add, pow_one, hs_succ, hs_zero, div_eq_mul_inv]; ring
  | succ m ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    show ((a₁ + a₂) * heckeRecursionSeq N (a₁ + a₂) (a₁ * a₂ / N) (m + 1) -
        a₁ * a₂ / N * heckeRecursionSeq N (a₁ + a₂) (a₁ * a₂ / N) m) / N = N⁻¹ ^ (m + 1 + 1) * hs a₁ a₂ (m + 1 + 1)
    rw [h0, h1, show m + 1 + 1 = m + 2 from rfl, hs_rec, div_eq_mul_inv, div_eq_mul_inv]
    ring

theorem torusFactor_neg (N lam om : ℂ) {m : ℤ} (hm : m < 0) : torusFactor N lam om m = 0 := by
  rw [torusFactor, if_neg (not_le.mpr hm)]

theorem ofReal_zpow_cpow (N : ℕ) (hN : 0 < N) (k : ℤ) (w : ℂ) :
    ((((N : ℝ) ^ k : ℝ)) : ℂ) ^ w = ((N : ℂ) ^ w) ^ k := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNk : (0 : ℝ) < (N : ℝ) ^ k := zpow_pos hN' k
  rw [← Complex.cpow_int_mul, Complex.cpow_def_of_ne_zero (by exact_mod_cast hNk.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hN'.ne'), ← Complex.ofReal_log hNk.le, Real.log_zpow,
    ← Complex.ofReal_natCast, ← Complex.ofReal_log hN'.le]
  push_cast
  ring_nf

theorem norm_eq_zpow {y : Fv v} {k : ℤ} (hy : Valued.v y = WithZero.exp k) :
    ‖y‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ k := by
  rw [NumberField.FinitePlace.norm_def, hy, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    show (WithZero.unzero (WithZero.exp_ne_zero : (WithZero.exp k : WithZero (Multiplicative ℤ)) ≠ 0)).toAdd = k
      from rfl]
  push_cast
  rfl

theorem coe_modulus_eq_norm (x : Fv v) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

theorem modulus_det_torus {π : Fv v} (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) (m k : ℤ) :
    ((modulus (((Matrix.GeneralLinearGroup.det (diagZ π hπ m * scalarPi π hπ ^ k) : (Fv v)ˣ)) : Fv v) : ℝ≥0) : ℝ) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(m + 2 * k)) := by
  rw [coe_modulus_eq_norm, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val]
  have h1 : (((Matrix.GeneralLinearGroup.det (diagZ π hπ m)) : (Fv v)ˣ) : Fv v) = π ^ m := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, show ((diagZ π hπ m : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![π ^ m, 0; 0, 1] from rfl,
      Matrix.det_fin_two_of]; ring
  have h2 : (((Matrix.GeneralLinearGroup.det (scalarPi π hπ)) : (Fv v)ˣ) : Fv v) = π ^ (2 : ℤ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, show ((scalarPi π hπ : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) = !![π, 0; 0, π] from rfl,
      Matrix.det_fin_two_of, zpow_two]; ring
  rw [h1, h2, ← zpow_mul, ← zpow_add₀ hπ, norm_zpow, norm_eq_zpow v hϖ, ← zpow_mul]
  congr 1
  ring

theorem W₂_mul_scalarPi_zpow {W₂ : G2 v → ℂ} {π : Fv v} {hπ : π ≠ 0} {z : ℂ} (hz : z ≠ 0)
    (hZ : ∀ g : G2 v, W₂ (g * scalarPi π hπ) = z * W₂ g) (g : G2 v) (k : ℤ) :
    W₂ (g * scalarPi π hπ ^ k) = z ^ k * W₂ g := by
  have hnat : ∀ (g : G2 v) (n : ℕ), W₂ (g * scalarPi π hπ ^ n) = z ^ n * W₂ g := by
    intro g n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, hZ, ih, pow_succ]; ring
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast, zpow_natCast, hnat]
  · have h := hnat (g * scalarPi π hπ ^ (-(n : ℤ))) n
    rw [mul_assoc, ← zpow_natCast, ← zpow_add, neg_add_cancel, zpow_zero, mul_one] at h
    rw [h, zpow_neg z, zpow_natCast z, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hz), one_mul]

end SlCR
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant.SlCR"

namespace SlCR

open scoped NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem psi_level_zero :
    (∀ x : Fv v, Valued.v x ≤ 1 → NumberField.StandardAddChar.psiLocal ℚ v x = 1) ∧
      ∃ y : Fv v, Valued.v y ≤ WithZero.exp (1 : ℤ) ∧ NumberField.StandardAddChar.psiLocal ℚ v y ≠ 1 := by
  have h0 : ∀ x : Fv v, Valued.v x ≤ 1 → NumberField.StandardAddChar.psiLocal ℚ v x = 1 := fun x hx =>
    LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ v x
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr hx)
  refine ⟨h0, ?_⟩
  have h := (LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v
    (NumberField.StandardAddChar.psiLocal ℚ v) ⟨0, fun x hx => h0 x (by rwa [WithZero.exp_zero] at hx)⟩
    (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v)).2
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat v, zero_add] at h

theorem term_algebra (N X Y z A h c : ℂ) (hN : N ≠ 0) (hX : X ≠ 0) (hY0 : Y ≠ 0) (hY : Y = z * X ^ 2)
    (m₁ m₂ e : ℕ) :
    c * N ^ ((m₁ : ℤ)) * (A * (z ^ ((m₂ : ℤ) - (e : ℤ)) * (N⁻¹ ^ m₁ * h)) *
        X ^ ((m₁ : ℤ) + 2 * ((m₂ : ℤ) - (e : ℤ)))) * Y ^ e = c * (A * h * X ^ m₁ * Y ^ m₂) := by
  have hX2 : X ^ 2 ≠ 0 := pow_ne_zero 2 hX
  have e1 : X ^ ((m₁ : ℤ) + 2 * ((m₂ : ℤ) - (e : ℤ))) = X ^ m₁ * (X ^ 2) ^ ((m₂ : ℤ) - (e : ℤ)) := by
    rw [zpow_add₀ hX, zpow_natCast, zpow_mul, zpow_ofNat]
  have e2 : z ^ ((m₂ : ℤ) - (e : ℤ)) * (X ^ 2) ^ ((m₂ : ℤ) - (e : ℤ)) * Y ^ e = Y ^ m₂ := by
    rw [← mul_zpow, ← hY, ← zpow_natCast Y e, ← zpow_add₀ hY0, sub_add_cancel, zpow_natCast]
  have e3 : N ^ ((m₁ : ℤ)) * N⁻¹ ^ m₁ = 1 := by
    rw [zpow_natCast, ← mul_pow, mul_inv_cancel₀ hN, one_pow]
  calc c * N ^ ((m₁ : ℤ)) * (A * (z ^ ((m₂ : ℤ) - (e : ℤ)) * (N⁻¹ ^ m₁ * h)) *
        X ^ ((m₁ : ℤ) + 2 * ((m₂ : ℤ) - (e : ℤ)))) * Y ^ e
      = c * (N ^ ((m₁ : ℤ)) * N⁻¹ ^ m₁) * A * h * X ^ m₁ *
          (z ^ ((m₂ : ℤ) - (e : ℤ)) * (X ^ 2) ^ ((m₂ : ℤ) - (e : ℤ)) * Y ^ e) := by rw [e1]; ring
    _ = c * (A * h * X ^ m₁ * Y ^ m₂) := by rw [e2, e3]; ring

def gmap (e : ℕ) (m : ℕ × ℕ) : ℤ × ℤ := ((m.1 : ℤ) + ((m.2 : ℤ) - (e : ℤ)), (m.2 : ℤ) - (e : ℤ))

theorem gmap_injective (e : ℕ) : Function.Injective (gmap e) := by
  intro m m' h
  simp only [gmap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  refine Prod.ext ?_ ?_ <;> omega

theorem not_mem_range_gmap {e : ℕ} {p : ℤ × ℤ} (hp : p ∉ Set.range (gmap e)) : p.1 - p.2 < 0 ∨ p.2 < -(e : ℤ) := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  exact hp ⟨((p.1 - p.2).toNat, (p.2 + e).toNat), by
    simp only [gmap]
    refine Prod.ext ?_ ?_ <;> simp only [] <;> omega⟩

theorem rpow_lt_of_lt {N ρ σ : ℝ} (hN : 1 < N) (hρ : 0 < ρ) (hσ : 1 / 2 - Real.log ρ / Real.log N < σ) :
    N ^ (1 / 2 - σ) < ρ := by
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have h1 : (1 / 2 - σ) * Real.log N < Real.log ρ := by
    have : 1 / 2 - σ < Real.log ρ / Real.log N := by linarith
    calc (1 / 2 - σ) * Real.log N < Real.log ρ / Real.log N * Real.log N := mul_lt_mul_of_pos_right this hlogN
      _ = Real.log ρ := div_mul_cancel₀ _ hlogN.ne'
  rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_log hρ, Real.exp_lt_exp, mul_comm]
  exact h1

end SlCR
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant.SlCR"

namespace SlCR

open scoped NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

def δf : G2 v → ℝ := fun g => ((modulus ((Matrix.GeneralLinearGroup.det g : (Fv v)ˣ) : Fv v) : ℝ≥0) : ℝ)

theorem δf_apply (g : G2 v) : δf v g = ((modulus ((Matrix.GeneralLinearGroup.det g : (Fv v)ˣ) : Fv v) : ℝ≥0) : ℝ) := rfl

theorem δf_N : ∀ n ∈ unip v, ∀ g : G2 v, δf v (n * g) = δf v g := by
  intro n hn g
  have hn' := unip_eq_unipotentGL2 v ⟨n, hn⟩
  simp only [δf_apply]
  rw [map_mul, show n = unipotentGL2 (((n : G2 v) : Matrix (Fin 2) (Fin 2) (Fv v)) 0 1) from hn', det_unipotentGL2, one_mul]

theorem modulus_det_K {k : G2 v} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    ((modulus (((Matrix.GeneralLinearGroup.det k) : (Fv v)ˣ) : Fv v) : ℝ≥0) : ℝ) = 1 := by
  have hv : Valued.v (((Matrix.GeneralLinearGroup.det k) : (Fv v)ˣ) : Fv v) = WithZero.exp (0 : ℤ) := by
    rw [WithZero.exp_zero]; exact v_det_eq_one_of_mem v hk
  rw [coe_modulus_eq_norm, norm_eq_zpow v hv, zpow_zero]

theorem δf_K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : G2 v, δf v (g * k) = δf v g := by
  intro k hk g
  simp only [δf_apply]
  rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul, modulus_det_K v hk, mul_one]

theorem δf_torus {π : Fv v} (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) (m k : ℤ) :
    δf v (diagZ π hπ m * scalarPi π hπ ^ k) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(m + 2 * k)) :=
  modulus_det_torus v hπ hϖ m k

theorem prod_N (θ : AddChar (Fv v) ℂ) (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn θ⁻¹ W) (W₂ : G2 v → ℂ)
    (hW₂ψ : ∀ (x : Fv v) (g : G2 v), W₂ (UnramifiedWhittaker.unipotent x * g) = θ x * W₂ g) :
    ∀ n ∈ unip v, ∀ g : G2 v,
      (fun g : G2 v => W (iotaGL g)) (n * g) * W₂ (n * g) = (fun g : G2 v => W (iotaGL g)) g * W₂ g := by
  intro n hn g
  obtain ⟨x, hx⟩ : ∃ x : Fv v, n = unipotentGL2 x := ⟨_, unip_eq_unipotentGL2 v ⟨n, hn⟩⟩
  show W (iotaGL (n * g)) * W₂ (n * g) = W (iotaGL g) * W₂ g
  rw [hx, map_mul, iotaGL_unipotentGL2, hW, add_zero, ← unipotent_eq, hW₂ψ, AddChar.inv_apply]
  calc θ (-x) * W (iotaGL g) * (θ x * W₂ g) = (θ (-x) * θ x) * (W (iotaGL g) * W₂ g) := by ring
    _ = W (iotaGL g) * W₂ g := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

theorem prod_K (W : LocalGL3 v → ℂ)
    (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, W (g * iotaGL k) = W g) (W₂ : G2 v → ℂ)
    (hW₂K : ∀ (k g : G2 v), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g) :
    ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : G2 v,
      (fun g : G2 v => W (iotaGL g)) (g * k) * W₂ (g * k) = (fun g : G2 v => W (iotaGL g)) g * W₂ g := by
  intro k hk g
  show W (iotaGL (g * k)) * W₂ (g * k) = W (iotaGL g) * W₂ g
  rw [map_mul, hK k hk, hW₂K k g hk]

def tcell (π : Fv v) (hπ : π ≠ 0) (p : ℤ × ℤ) : G2 v := diagZ π hπ (p.1 - p.2) * scalarPi π hπ ^ p.2

theorem cell_term {π : Fv v} (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ))
    (W : LocalGL3 v → ℂ) (W₂ : G2 v → ℂ) (a₁ a₂ z : ℂ) (hz0 : z ≠ 0)
    (hz : z = a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ))
    (hZ : ∀ g : G2 v, W₂ (g * scalarPi π hπ) = z * W₂ g)
    (hT : ∀ m : ℤ, W₂ (diagZ π hπ m) = torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m)
    (s X Y : ℂ) (hX : X = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2 - s)) (hY : Y = z * X ^ 2) (c : ℂ) (e : ℕ)
    (m : ℕ × ℕ) :
    c * (Ideal.absNorm v.asIdeal : ℂ) ^ ((gmap e m).1 - (gmap e m).2) *
        ((W (iotaGL (tcell v π hπ (gmap e m))) * W₂ (tcell v π hπ (gmap e m))) *
          ((δf v (tcell v π hπ (gmap e m)) : ℝ) : ℂ) ^ (s - 1 / 2)) * Y ^ e =
      c * (W (iotaGL (scalarPi π hπ ^ ((m.2 : ℤ) - (e : ℤ)) * diagUnitGL2 (Units.mk0 π hπ ^ (m.1 : ℤ)))) *
        hs a₁ a₂ m.1 * X ^ m.1 * Y ^ m.2) := by
  have hN : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  have hNc : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hX0 : X ≠ 0 := by rw [hX]; intro h; rw [Complex.cpow_eq_zero_iff] at h; exact hNc h.1
  have hY0 : Y ≠ 0 := by rw [hY]; exact mul_ne_zero hz0 (pow_ne_zero 2 hX0)
  have e12 : (gmap e m).1 - (gmap e m).2 = (m.1 : ℤ) := by simp only [gmap]; ring
  have e2 : (gmap e m).2 = (m.2 : ℤ) - (e : ℤ) := rfl

  have hWι : W (iotaGL (tcell v π hπ (gmap e m))) =
      W (iotaGL (scalarPi π hπ ^ ((m.2 : ℤ) - (e : ℤ)) * diagUnitGL2 (Units.mk0 π hπ ^ (m.1 : ℤ)))) := by
    rw [tcell, e12, e2, diagZ_mul_scalarPi_zpow]
  have hW₂ : W₂ (tcell v π hπ (gmap e m)) =
      z ^ ((m.2 : ℤ) - (e : ℤ)) * (((Ideal.absNorm v.asIdeal : ℂ))⁻¹ ^ m.1 * hs a₁ a₂ m.1) := by
    rw [tcell, e12, e2, W₂_mul_scalarPi_zpow v hz0 hZ, hT, torusFactor_eq _ hNc]
  have hδ : ((δf v (tcell v π hπ (gmap e m)) : ℝ) : ℂ) ^ (s - 1 / 2) = X ^ ((m.1 : ℤ) + 2 * ((m.2 : ℤ) - (e : ℤ))) := by
    rw [tcell, e12, e2, δf_torus v hπ hϖ, ofReal_zpow_cpow _ hN, hX,
      show (1 : ℂ) / 2 - s = -(s - 1 / 2) by ring, Complex.cpow_neg, inv_zpow']
  rw [e12, hWι, hW₂, hδ]
  exact term_algebra _ X Y z _ _ c hNc hX0 hY0 hY m.1 m.2 e

theorem cell_term_vanish {π : Fv v} (hπ : π ≠ 0) (W : LocalGL3 v → ℂ) (W₂ : G2 v → ℂ) (a₁ a₂ z : ℂ) (hz0 : z ≠ 0)
    (hZ : ∀ g : G2 v, W₂ (g * scalarPi π hπ) = z * W₂ g)
    (hT : ∀ m : ℤ, W₂ (diagZ π hπ m) = torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m)
    (e : ℕ) (hsupp : ∀ n₁ n₂ : ℤ, (n₁ < 0 ∨ n₂ < -(e : ℤ)) →
      W (iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁))) = 0)
    (s Y : ℂ) (c : ℂ) (p : ℤ × ℤ) (hp : p ∉ Set.range (gmap e)) :
    c * (Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2) *
        ((W (iotaGL (tcell v π hπ p)) * W₂ (tcell v π hπ p)) * ((δf v (tcell v π hπ p) : ℝ) : ℂ) ^ (s - 1 / 2)) * Y ^ e = 0 := by
  rcases not_mem_range_gmap hp with h | h
  · have : W₂ (tcell v π hπ p) = 0 := by
      rw [tcell, W₂_mul_scalarPi_zpow v hz0 hZ, hT, torusFactor_neg _ _ _ h, mul_zero]
    rw [this]; ring
  · have : W (iotaGL (tcell v π hπ p)) = 0 := by
      rw [tcell, diagZ_mul_scalarPi_zpow]; exact hsupp _ _ (Or.inr h)
    rw [this]; ring

theorem eval_bind₁_q (Nc X Y z a₁ a₂ : ℂ) (hz : z = a₁ * a₂ / Nc) (hY : Y = z * X ^ 2) (P : MvPolynomial (Fin 4) ℂ) :
    MvPolynomial.eval (![X, a₁, a₂] : Fin 3 → ℂ)
        (MvPolynomial.bind₁ (![MvPolynomial.X 0, MvPolynomial.C Nc⁻¹ * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 0 ^ 2,
          MvPolynomial.X 1, MvPolynomial.X 2] : Fin 4 → MvPolynomial (Fin 3) ℂ) P) =
      MvPolynomial.eval (![X, Y, a₁, a₂] : Fin 4 → ℂ) P := by
  have hfun : (fun i : Fin 4 => MvPolynomial.eval₂Hom (RingHom.id ℂ) (![X, a₁, a₂] : Fin 3 → ℂ)
      ((![MvPolynomial.X 0, MvPolynomial.C Nc⁻¹ * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 0 ^ 2,
          MvPolynomial.X 1, MvPolynomial.X 2] : Fin 4 → MvPolynomial (Fin 3) ℂ) i)) = ![X, Y, a₁, a₂] := by
    funext i
    fin_cases i <;> simp <;> (rw [hY, hz]; ring)
  show MvPolynomial.eval₂Hom (RingHom.id ℂ) (![X, a₁, a₂] : Fin 3 → ℂ) (MvPolynomial.bind₁ _ P) = _
  rw [MvPolynomial.eval₂Hom_bind₁, ← hfun]
  rfl

theorem tail {T : ℤ × ℤ → ℂ} {I : ℂ} (hT : HasSum T I) (e : ℕ) (Ye c : ℂ) (f : ℕ × ℕ → ℂ)
    (hvan : ∀ p : ℤ × ℤ, p ∉ Set.range (gmap e) → T p * Ye = 0)
    (hval : ∀ m : ℕ × ℕ, T (gmap e m) * Ye = c * f m) :
    HasSum (fun m : ℕ × ℕ => c * f m) (I * Ye) := by
  have h1 : HasSum (fun p : ℤ × ℤ => T p * Ye) (I * Ye) := hT.mul_right Ye
  have h2 : HasSum ((fun p : ℤ × ℤ => T p * Ye) ∘ gmap e) (I * Ye) :=
    ((gmap_injective e).hasSum_iff (f := fun p : ℤ × ℤ => T p * Ye) hvan).mpr h1
  have h3 : (fun p : ℤ × ℤ => T p * Ye) ∘ gmap e = fun m => c * f m := funext fun m => hval m
  rwa [h3] at h2

theorem final_algebra (I Ye c S Dp E4 E3 : ℂ) (h5 : c * S = I * Ye) (hident : S * Dp = E4) (hq : E3 = E4) :
    I * (Dp * Ye) = c * E3 := by
  rw [hq, ← hident, show I * (Dp * Ye) = (I * Ye) * Dp by ring, ← h5]
  ring

end SlCR
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant.SlCR"

namespace SlCR

open scoped NNReal

theorem main_core (v : HeightOneSpectrum (𝓞 ℚ))
    (θ : AddChar (v.adicCompletion ℚ) ℂ)
    (hθ : θ = NumberField.StandardAddChar.psiLocal ℚ v ∨ θ = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (π : v.adicCompletion ℚ) (hπ : π ≠ 0) (hϖ : Valued.v π = WithZero.exp (-1 : ℤ))
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn θ⁻¹ W)
    (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, W (g * iotaGL k) = W g)
    (hTA : ∃ (e : ℕ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n₁ n₂ : ℤ, (n₁ < 0 ∨ n₂ < -(e : ℤ)) →
        W (iotaGL (scalarPi π hπ ^ n₂ * diagUnitGL2 (Units.mk0 π hπ ^ n₁))) = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l *
            W (iotaGL (scalarPi π hπ ^ ((m₂ : ℤ) - (l : ℤ) - (e : ℤ)) * diagUnitGL2 (Units.mk0 π hπ ^ ((m₁ : ℤ) - (i : ℤ))))) = 0))
    (hcell : letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ.IsHaarMeasure]
      (μN : Measure (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure]
      [μN.IsMulRightInvariant]
      (δ : GL (Fin 2) (v.adicCompletion ℚ) → ℝ)
      (_hδN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δ (n * g) = δ g)
      (_hδK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δ (g * k) = δ g)
      (s : ℂ) (W F : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
      (_hN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W (n * g) * F (n * g) = W g * F g)
      (_hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W (g * k) * F (g * k) = W g * F g)
      (_hint : Integrable
        (fun g : GL (Fin 2) (v.adicCompletion ℚ) => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ.withDensity
          (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))),
      HasSum (fun p : ℤ × ℤ =>
          (((μ.withDensity
                (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
              {g : GL (Fin 2) (v.adicCompletion ℚ) |
                ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                  ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ) *
            ((Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2)) *
            ((W (diagZ π hπ (p.1 - p.2) *
                  scalarPi π hπ ^ p.2) *
                F (diagZ π hπ (p.1 - p.2) *
                  scalarPi π hπ ^ p.2)) *
              ((δ (diagZ π hπ (p.1 - p.2) *
                  scalarPi π hπ ^ p.2) :
                    ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.rsLocalIntegral μ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN δ s W
          F)) :
    ∃ (P : MvPolynomial (Fin 3) ℂ) (D₁ D₂ : Polynomial ℂ) (e : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
    ∃ c : ℂ,
    ∀ (a₁ a₂ : ℂ) (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
      (_hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
        W₂ (unipotent x * g) = θ x * W₂ g)
      (_hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
      (_hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        W₂ (g * scalarPi π hπ) = a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
      (_hW₂T : ∀ m : ℤ, W₂ (diagZ π hπ m) = torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m),
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (W (iotaGL g) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) →
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
          s (fun g => W (iotaGL g)) W₂ *
        (D₁.eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s)) * D₁.eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s)) *
          D₂.eval (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s)) ^ 2) *
          (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s)) ^ 2) ^ e) =
      c * MvPolynomial.eval (![(Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s), a₁, a₂] : Fin 3 → ℂ) P := by
  classical
  letI iG : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := localGLBorel ℚ v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ v
  obtain ⟨e, D₁, D₂, M, hD₁0, hD₂0, hsupp, hrec⟩ := hTA

  obtain ⟨A', hA'⟩ : ∃ A' : ℤ × ℤ → ℂ, A' = fun n => W (iotaGL (scalarPi π hπ ^ (n.2 - (e : ℤ)) *
    diagUnitGL2 (Units.mk0 π hπ ^ n.1))) := ⟨_, rfl⟩
  have hsupp' : ∀ n : ℤ × ℤ, (n.1 < 0 ∨ n.2 < 0) → A' n = 0 := by
    intro n hn
    simp only [hA']
    exact hsupp n.1 (n.2 - e) (by rcases hn with h | h; exact Or.inl h; exact Or.inr (by omega))
  have hrec' : ∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
      ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
        D₁.coeff i * D₂.coeff l * A' (0 + (m₁ : ℤ) - (i : ℤ), 0 + (m₂ : ℤ) - (l : ℤ)) = 0 := by
    intro m₁ m₂ hM
    simp only [hA', zero_add]
    exact hrec m₁ m₂ hM
  obtain ⟨P, hP⟩ := Polynomial.exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence
    A' 0 D₁ D₂ M hD₁0 hD₂0 hsupp' hrec'

  obtain ⟨Nc, hNc⟩ : ∃ Nc : ℂ, Nc = (Ideal.absNorm v.asIdeal : ℂ) := ⟨_, rfl⟩
  have hNpos : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  have hN1 : 1 < Ideal.absNorm v.asIdeal := by
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    omega
  have hNc0 : Nc ≠ 0 := by rw [hNc]; exact_mod_cast hNpos.ne'
  let q : Fin 4 → MvPolynomial (Fin 3) ℂ :=
    ![MvPolynomial.X 0, MvPolynomial.C Nc⁻¹ * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 0 ^ 2,
      MvPolynomial.X 1, MvPolynomial.X 2]
  refine ⟨MvPolynomial.bind₁ q P, D₁, D₂, e, hD₁0, hD₂0, ?_⟩
  intro μ₂ _ μN _
  haveI : μN.IsMulRightInvariant := SlCR.isMulRightInvariant_unip v μN

  refine ⟨(((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
      {g : GL (Fin 2) (v.adicCompletion ℚ) |
        ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ), ?_⟩
  intro a₁ a₂ W₂ hW₂ψ hW₂K hW₂Z hW₂T

  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = a₁ * a₂ / Nc := ⟨_, rfl⟩
  have hz0 : z ≠ 0 := by
    intro h0
    have h1 := hW₂T 0
    rw [UnramifiedWhittaker.torusFactor, if_pos le_rfl, Int.toNat_zero] at h1
    have hd : diagZ π hπ 0 = 1 := by
      apply Units.ext
      show (!![π ^ (0 : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have h2 := hW₂Z (scalarPi π hπ)⁻¹
    rw [inv_mul_cancel, ← hNc, ← hz, h0, zero_mul, ← hd, h1] at h2
    have h3 : (1 : ℂ) = 0 := by simpa [heckeRecursionSeq] using h2
    exact one_ne_zero h3

  obtain ⟨r, hr, hPr⟩ := hP a₁ a₂
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = min (min r 1) (r / (‖z‖ + 1)) := ⟨_, rfl⟩
  have hz1 : 0 < ‖z‖ + 1 := by positivity
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; exact lt_min (lt_min hr one_pos) (div_pos hr hz1)
  refine ⟨1 / 2 - Real.log ρ₀ / Real.log (Ideal.absNorm v.asIdeal : ℝ), ?_⟩
  intro s hs hint
  obtain ⟨X, hX⟩ : ∃ X : ℂ, X = Nc ^ ((1 : ℂ) / 2 - s) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℂ, Y = z * X ^ 2 := ⟨_, rfl⟩
  have hNR : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hN1
  have hXnorm : ‖X‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 - s.re) := by
    rw [hX, hNc, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1
    simp [Complex.sub_re, Complex.div_re]
  have hXlt : ‖X‖ < ρ₀ := by rw [hXnorm]; exact SlCR.rpow_lt_of_lt hNR hρ₀pos hs
  have hXr : ‖X‖ < r := hXlt.trans_le (by rw [hρ₀]; exact (min_le_left _ _).trans (min_le_left _ _))
  have hX1 : ‖X‖ < 1 := hXlt.trans_le (by rw [hρ₀]; exact (min_le_left _ _).trans (min_le_right _ _))
  have hYr : ‖Y‖ < r := by
    rw [hY, norm_mul, norm_pow]
    have hX2 : ‖X‖ ^ 2 ≤ ‖X‖ := by nlinarith [norm_nonneg X]
    calc ‖z‖ * ‖X‖ ^ 2 ≤ (‖z‖ + 1) * ‖X‖ := by nlinarith [norm_nonneg X, norm_nonneg z]
      _ < (‖z‖ + 1) * (r / (‖z‖ + 1)) := by
          exact mul_lt_mul_of_pos_left (hXlt.trans_le (by rw [hρ₀]; exact min_le_right _ _)) hz1
      _ = r := by field_simp
  have hX0 : X ≠ 0 := by
    rw [hX]; intro h; rw [Complex.cpow_eq_zero_iff] at h; exact hNc0 h.1
  have hY0 : Y ≠ 0 := by rw [hY]; exact mul_ne_zero hz0 (pow_ne_zero 2 hX0)
  obtain ⟨hsummable, hident⟩ := hPr X Y hXr hYr
  simp only [hA', zero_add] at hsummable hident

  have hz' : z = a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) := by rw [hz, hNc]
  have hZ' : ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W₂ (g * scalarPi π hπ) = z * W₂ g := by
    intro g; rw [hW₂Z g, hz']
  have hX' : X = (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2 - s) := by rw [hX, hNc]
  have hsum := hcell μ₂ μN (SlCR.δf v) (SlCR.δf_N v) (SlCR.δf_K v) s (fun g => W (iotaGL g)) W₂
    (SlCR.prod_N v θ W hW W₂ hW₂ψ) (SlCR.prod_K v W hK W₂ hW₂K) hint
  have h4 := SlCR.tail hsum e (Y ^ e) _ _
    (fun p hp => SlCR.cell_term_vanish v hπ W W₂ a₁ a₂ z hz0 hZ' hW₂T e hsupp s Y _ p hp)
    (fun m => SlCR.cell_term v hπ hϖ W W₂ a₁ a₂ z hz0 hz' hZ' hW₂T s X Y hX' hY _ e m)
  have h5 := (hsummable.of_norm.hasSum.mul_left _).unique h4
  have hq := SlCR.eval_bind₁_q Nc X Y z a₁ a₂ hz hY P
  subst hY hX hz hNc
  exact SlCR.final_algebra _ _ _ _ _ _ _ h5 hident hq

end SlCR
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant.SlCR"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant.SlCR"

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (θ : AddChar (v.adicCompletion ℚ) ℂ)
    (hθ : θ = NumberField.StandardAddChar.psiLocal ℚ v ∨ θ = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn θ⁻¹ W)
    (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ g : LocalGL3 v, W (g * iotaGL k) = W g)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) :
    ∃ (P : MvPolynomial (Fin 3) ℂ) (D₁ D₂ : Polynomial ℂ) (e : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
    ∃ c : ℂ,
    ∀ (a₁ a₂ : ℂ) (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
      (_hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
        W₂ (unipotent x * g) = θ x * W₂ g)
      (_hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
      (_hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
      (_hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) = torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m),
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (W (iotaGL g) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) →
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
          s (fun g => W (iotaGL g)) W₂ *
        (D₁.eval (a₁ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s)) * D₁.eval (a₂ * (Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s)) *
          D₂.eval (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s)) ^ 2) *
          (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s)) ^ 2) ^ e) =
      c * MvPolynomial.eval (![(Ideal.absNorm v.asIdeal : ℂ) ^ (1 / 2 - s), a₁, a₂] : Fin 3 → ℂ) P := by

  obtain ⟨hψ0, hψ1⟩ := SlCR.psi_level_zero v
  have hθ'0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → θ⁻¹ x = 1 := by
    intro x hx
    rcases hθ with rfl | rfl
    · rw [AddChar.inv_apply]; exact hψ0 (-x) (by rwa [Valuation.map_neg])
    · rw [inv_inv]; exact hψ0 x hx
  have hθ'1 : ∃ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (1 : ℤ) ∧ θ⁻¹ y ≠ 1 := by
    obtain ⟨y, hy, hy1⟩ := hψ1
    rcases hθ with rfl | rfl
    · exact ⟨-y, by rwa [Valuation.map_neg], by rwa [AddChar.inv_apply, neg_neg]⟩
    · exact ⟨y, hy, by rwa [inv_inv]⟩
  obtain ⟨Uv, hUo, hUv⟩ := hsm
  obtain ⟨⟨C₁, hC₁, hF₁⟩, ⟨C₂, hC₂, hF₂⟩⟩ :=
    LanglandsTunnell.CubicInduction.exists_polynomial_sum_coeff_smul_rightTranslate_pow_mem_span_radical_of_admissible
      v W ⟨Uv, hUo, hUv⟩ hadm hπ hϖ W (SlCR.mem_gl3CyclicSubspace_self v W)
  obtain ⟨hV1, hV2⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_torus_eq_zero_of_mem_span_radical_of_isGL3PsiWhittakerFn
      v θ⁻¹ ⟨0, fun x hx => hθ'0 x (by rwa [WithZero.exp_zero] at hx)⟩ W hW hπ hϖ
  obtain ⟨N₁, hN₁⟩ := hV1 _ hF₁
  obtain ⟨N₂, hN₂⟩ := hV2 _ hF₂
  exact SlCR.main_core v θ hθ _ hπ hϖ W hW hK
    (SlCR.torus_array v θ⁻¹ hθ'1 _ hπ hϖ W hW hK Uv hUo hUv C₁ C₂ hC₁ hC₂ N₁ N₂ hN₁ hN₂)
    (LanglandsTunnell.RankinSelberg.hasSum_cell_terms_rsLocalIntegral v hπ hϖ)

end S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_mvPolynomial_forall_rsLocalIntegral_mul_eq_eval_of_iotaGL_invariant (solution)
