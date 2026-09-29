-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/050db1ae-608b-542b-ad71-7c4acc96fb89

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.Analysis.Matrix.Normed
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal NNReal

noncomputable section

namespace E3ReduceSupplyF

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ

theorem level_zero :
    (∀ x : Qp, Valued.v x ≤ WithZero.exp (0 : ℤ) → NumberField.StandardAddChar.psiLocal ℚ p x = 1) ∧
      ∃ x : Qp, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ NumberField.StandardAddChar.psiLocal ℚ p x ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : Qp, Valued.v x ≤ WithZero.exp k → NumberField.StandardAddChar.psiLocal ℚ p x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p
    (NumberField.StandardAddChar.psiLocal ℚ p) hk (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h

theorem level_zero_inv :
    (∀ x : Qp, Valued.v x ≤ WithZero.exp (0 : ℤ) → (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x = 1) ∧
      ∃ x : Qp, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x ≠ 1 := by
  obtain ⟨h0, h1⟩ := level_zero p
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [AddChar.inv_apply]; exact h0 (-x) (by rwa [Valuation.map_neg])
  · obtain ⟨x, hx, hne⟩ := h1
    refine ⟨-x, by rwa [Valuation.map_neg], ?_⟩
    rwa [AddChar.inv_apply, neg_neg]

theorem selfDualHaarAt_eq :
    selfDualHaarAt ℚ p = @Measure.addHaarMeasure (p.adicCompletion ℚ) _ _ _ (localBorel ℚ p)
      (borelSpace_localBorel ℚ p) (integersPositiveCompacts ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  unfold selfDualHaarAt
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p]
  simp

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  rw [selfDualHaarAt_eq p]
  infer_instance

theorem isSchwartzBruhat_tateFourier_psiLocal_inv (φ : Qp → ℂ) (hφ : IsSchwartzBruhat φ) :
    letI := localBorel ℚ p
    IsSchwartzBruhat (tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨h0, h1⟩ := level_zero_inv p
  exact LanglandsTunnell.TateLocal.isSchwartzBruhat_tateFourier ℚ p (selfDualHaarAt ℚ p)
    ((NumberField.StandardAddChar.psiLocal ℚ p)⁻¹) 0 h0 h1 φ hφ

theorem continuous_tateFourier_of_isSchwartzBruhat (φ : Qp → ℂ) (hφ : IsSchwartzBruhat φ) :
    letI := localBorel ℚ p
    Continuous (tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ) :=
  (isSchwartzBruhat_tateFourier_psiLocal_inv p φ hφ).1.continuous

end E3ReduceSupplyF

namespace RCgB

section LocalField

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)

def qR : ℝ := ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ)

theorem one_lt_qR : 1 < qR v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [qR]; exact_mod_cast this

theorem qR_pos : 0 < qR v := zero_lt_one.trans (one_lt_qR v)

theorem qR_ne_zero : qR v ≠ 0 := (qR_pos v).ne'

theorem norm_le_one_iff (x : F) : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := by
  rw [NumberField.FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe]
  exact WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)

theorem norm_eq_one_iff (x : F) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  rw [NumberField.FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'

theorem norm_eq_zpow_of_v_eq_exp (x : F) (m : ℤ) (hx : Valued.v x = WithZero.exp m) : ‖x‖ = qR v ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    NNReal.coe_zpow, qR]
  congr 1

theorem coe_modulus_eq_norm (x : F) : ((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

variable {v}

theorem uniformizer_ne_zero {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) : ϖ ≠ 0 := by
  intro h
  rw [h, map_zero] at hϖ
  exact WithZero.exp_ne_zero hϖ.symm

theorem v_uniformizer_zpow {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]

theorem norm_uniformizer_zpow {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    ‖ϖ ^ k‖ = qR v ^ (-k) :=
  norm_eq_zpow_of_v_eq_exp v _ _ (v_uniformizer_zpow hϖ k)

end LocalField

section Kzero

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

abbrev kzero : Subgroup G := AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ (O)) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : G) :
    k ∈ kzero v ↔ (∀ i j, (k : Mat) i j ∈ (O)) ∧ ∀ i j, ((k⁻¹ : G) : Mat) i j ∈ (O) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral v h1, isLocalLevelOne_top_of_integral v h2⟩

theorem coe_kzero_eq_localIntegralSet : ((kzero v : Subgroup G) : Set G) = localIntegralSet ℚ v := by
  ext k
  rw [SetLike.mem_coe, mem_kzero_iff, mem_localIntegralSet]

theorem isOpen_kzero : IsOpen ((kzero v : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isOpen_localIntegralSet ℚ v

theorem isCompact_kzero : IsCompact ((kzero v : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isCompact_localIntegralSet ℚ v

variable {v}

theorem v_entry_le_one {k : G} (hk : k ∈ kzero v) (i j : Fin 2) : Valued.v ((k : Mat) i j) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (((mem_kzero_iff v k).mp hk).1 i j)

theorem norm_entry_le_one {k : G} (hk : k ∈ kzero v) (i j : Fin 2) : ‖(k : Mat) i j‖ ≤ 1 :=
  (norm_le_one_iff v _).mpr (v_entry_le_one hk i j)

theorem v_det_le_one_of_integral {m : Mat} (h : ∀ i j, Valued.v (m i j) ≤ 1) : Valued.v m.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  calc Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0)
      ≤ max (Valued.v (m 0 0 * m 1 1)) (Valued.v (m 0 1 * m 1 0)) := Valuation.map_sub _ _ _
    _ ≤ 1 := by
        refine max_le ?_ ?_
        · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
        · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

theorem v_det_eq_one {k : G} (hk : k ∈ kzero v) : Valued.v (k : Mat).det = 1 := by
  have h1 : Valued.v (k : Mat).det ≤ 1 := v_det_le_one_of_integral (v_entry_le_one hk)
  have h2 : Valued.v ((k⁻¹ : G) : Mat).det ≤ 1 := v_det_le_one_of_integral (v_entry_le_one (inv_mem hk))
  have hprod : Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det := hprod.symm
    _ ≤ Valued.v (k : Mat).det * 1 := by gcongr
    _ = Valued.v (k : Mat).det := mul_one _

theorem norm_det_eq_one {k : G} (hk : k ∈ kzero v) : ‖(k : Mat).det‖ = 1 :=
  (norm_eq_one_iff v _).mpr (v_det_eq_one hk)

theorem max_norm_bottom_row_eq_one {k : G} (hk : k ∈ kzero v) :
    max ‖(k : Mat) 1 0‖ ‖(k : Mat) 1 1‖ = 1 := by
  have hle := v_entry_le_one hk

  have hdet : (1 : WithZero (Multiplicative ℤ)) ≤ max (Valued.v ((k : Mat) 1 0)) (Valued.v ((k : Mat) 1 1)) := by
    rw [← v_det_eq_one hk, Matrix.det_fin_two]
    calc Valued.v ((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0)
        ≤ max (Valued.v ((k : Mat) 0 0 * (k : Mat) 1 1)) (Valued.v ((k : Mat) 0 1 * (k : Mat) 1 0)) :=
          Valuation.map_sub _ _ _
      _ ≤ max (Valued.v ((k : Mat) 1 1)) (Valued.v ((k : Mat) 1 0)) := by
          refine max_le_max ?_ ?_
          · rw [map_mul]; exact mul_le_of_le_one_left' (hle 0 0)
          · rw [map_mul]; exact mul_le_of_le_one_left' (hle 0 1)
      _ = max (Valued.v ((k : Mat) 1 0)) (Valued.v ((k : Mat) 1 1)) := max_comm _ _
  have hn0 : ‖(k : Mat) 1 0‖ ≤ 1 := norm_entry_le_one hk 1 0
  have hn1 : ‖(k : Mat) 1 1‖ ≤ 1 := norm_entry_le_one hk 1 1
  rcases le_max_iff.mp hdet with h | h
  · have h' : Valued.v ((k : Mat) 1 0) = 1 := le_antisymm (hle 1 0) h
    rw [(norm_eq_one_iff v _).mpr h']
    exact max_eq_left hn1
  · have h' : Valued.v ((k : Mat) 1 1) = 1 := le_antisymm (hle 1 1) h
    rw [(norm_eq_one_iff v _).mpr h']
    exact max_eq_right hn0

end Kzero

section Torus

open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def diagU (a b : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : G where
  val := !![(a : F), 0; 0, (b : F)]
  inv := !![((a⁻¹ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F), 0;
    0, ((b⁻¹ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem coe_diagU (a b : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
    ((diagU v a b : G) : Mat) = !![(a : F), 0; 0, (b : F)] := rfl

theorem diagU_inv (a b : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
    (diagU v a b)⁻¹ = diagU v a⁻¹ b⁻¹ := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  change ((diagU v a b : G) : Mat) * ((diagU v a⁻¹ b⁻¹ : G) : Mat) = 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagU_mul (a b a' b' : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
    diagU v a b * diagU v a' b' = diagU v (a * a') (b * b') := by
  refine Units.ext ?_
  change ((diagU v a b : G) : Mat) * ((diagU v a' b' : G) : Mat) = ((diagU v (a * a') (b * b') : G) : Mat)
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def diagUHom : (HeightOneSpectrum.adicCompletion ℚ v)ˣ × (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* G where
  toFun p := diagU v p.1 p.2
  map_one' := by
    refine Units.ext ?_
    change ((diagU v 1 1 : G) : Mat) = 1
    rw [coe_diagU]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' p p' := (diagU_mul v p.1 p.2 p'.1 p'.2).symm

theorem diagU_zpow (a b : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (n : ℤ) :
    (diagU v a b) ^ n = diagU v (a ^ n) (b ^ n) := by
  change (diagUHom v (a, b)) ^ n = diagUHom v ((a, b) ^ n)
  rw [map_zpow]

variable {v}
variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

def piUnit (hπ : algebraMap (O) (F) ϖ ≠ 0) : (HeightOneSpectrum.adicCompletion ℚ v)ˣ :=
  Units.mk0 (algebraMap (O) (F) ϖ) hπ

@[scoped simp] theorem coe_piUnit (hπ : algebraMap (O) (F) ϖ ≠ 0) : ((piUnit hπ : _ˣ) : F) = algebraMap (O) (F) ϖ := rfl

theorem coe_piUnit_zpow (hπ : algebraMap (O) (F) ϖ ≠ 0) (k : ℤ) :
    (((piUnit hπ) ^ k : _ˣ) : F) = (algebraMap (O) (F) ϖ) ^ k := by
  rw [Units.val_zpow_eq_zpow_val, coe_piUnit]

theorem scalarPi_eq_diagU (hπ : algebraMap (O) (F) ϖ ≠ 0) :
    scalarPi (algebraMap (O) (F) ϖ) hπ = diagU v (piUnit hπ) (piUnit hπ) := by
  refine Units.ext ?_
  rw [coe_diagU]
  simp [scalarPi, piUnit]

theorem diagZ_eq_diagU (hπ : algebraMap (O) (F) ϖ ≠ 0) (d : ℤ) :
    diagZ (algebraMap (O) (F) ϖ) hπ d = diagU v (piUnit hπ ^ d) 1 := by
  refine Units.ext ?_
  rw [coe_diagU]
  simp [diagZ, piUnit, Units.val_zpow_eq_zpow_val]

theorem shellRep_eq_diagU (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 =
      diagU v (piUnit hπ ^ (dn.2 + dn.1)) (piUnit hπ ^ dn.2) := by
  rw [scalarPi_eq_diagU hπ, diagZ_eq_diagU hπ, diagU_zpow, diagU_mul, zpow_add, mul_one]

theorem shellRep_eq_diagZ_mul (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 =
      diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 := by
  rw [scalarPi_eq_diagU hπ, diagZ_eq_diagU hπ, diagU_zpow, diagU_mul, diagU_mul, mul_one, one_mul, mul_comm]

theorem scalarPi_eq_scalar (hπ : algebraMap (O) (F) ϖ ≠ 0) :
    scalarPi (algebraMap (O) (F) ϖ) hπ = Matrix.GeneralLinearGroup.scalar (Fin 2) (piUnit hπ) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarPi, piUnit, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]

theorem scalarPi_zpow_eq_scalar (hπ : algebraMap (O) (F) ϖ ≠ 0) (n : ℤ) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ n = Matrix.GeneralLinearGroup.scalar (Fin 2) (piUnit hπ ^ n) := by
  rw [scalarPi_eq_scalar hπ, map_zpow]

end Torus

end RCgB
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport.RCgB"

namespace BPhi

open NumberField.StandardAddChar

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem exists_radius_of_isLocallyConstant_of_hasCompactSupport {X : Type*} [MetricSpace X]
    (f : X → ℂ) (hlc : IsLocallyConstant f) (hcs : HasCompactSupport f) :
    ∃ δ > 0, ∀ x y : X, dist x y < δ → f x = f y := by
  obtain ⟨δ, hδ, hU⟩ := lebesgue_number_lemma_of_metric (ι := X) (c := fun i => {y | f y = f i}) hcs
    (fun i => hlc.isOpen_fiber (f i)) (fun x _ => Set.mem_iUnion.2 ⟨x, rfl⟩)
  refine ⟨δ, hδ, ?_⟩
  have key : ∀ x ∈ tsupport f, ∀ y, dist x y < δ → f x = f y := by
    intro x hx y hxy
    obtain ⟨i, hi⟩ := hU x hx
    have h1 : f x = f i := hi (Metric.mem_ball_self hδ)
    have h2 : f y = f i := hi (by rw [Metric.mem_ball, dist_comm]; exact hxy)
    rw [h1, h2]
  intro x y hxy
  by_cases hx : x ∈ tsupport f
  · exact key x hx y hxy
  by_cases hy : y ∈ tsupport f
  · exact (key y hy x (by rw [dist_comm]; exact hxy)).symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

theorem isLocallyConstant_psiLocal : IsLocallyConstant (fun t : F => (psiLocal ℚ p t : ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen ((fun y : F => y - x) ⁻¹' (p.adicCompletionIntegers ℚ : Set F)) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_id.sub continuous_const)
  have hmem : x ∈ (fun y : F => y - x) ⁻¹' (p.adicCompletionIntegers ℚ : Set F) := by
    simp only [Set.mem_preimage, sub_self, SetLike.mem_coe]; exact zero_mem _
  filter_upwards [hopen.mem_nhds hmem] with y hy
  have h1 : psiLocal ℚ p (y - x) = 1 := by
    apply (E3ReduceSupplyF.level_zero p).1
    rw [WithZero.exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hy
  have : y = (y - x) + x := by ring
  rw [this, AddChar.map_add_eq_mul, h1, one_mul]

theorem continuous_psiLocal : Continuous (fun t : F => (psiLocal ℚ p t : ℂ)) :=
  (isLocallyConstant_psiLocal p).continuous

theorem norm_le_zpow_iff {ϖ : O} (hϖ : Valued.v (algebraMap (O) (F) ϖ) = WithZero.exp (-1 : ℤ)) (x : F) (m : ℤ) :
    ‖x‖ ≤ RCgB.qR p ^ m ↔ Valued.v x ≤ WithZero.exp m := by
  have h := RCgB.norm_uniformizer_zpow (v := p) hϖ (-m)
  rw [neg_neg] at h
  rw [← h, Valued.toNormedField.norm_le_iff, RCgB.v_uniformizer_zpow hϖ, neg_neg]

theorem exists_constancy_exponent (Φ : Mat → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ c : ℤ, ∀ X Y : Mat, (∀ i j, ‖Y i j‖ ≤ RCgB.qR p ^ (-c)) → Φ (X + Y) = Φ X := by
  letI : NormedAddCommGroup Mat := Matrix.normedAddCommGroup
  obtain ⟨δ, hδ, hunif⟩ := exists_radius_of_isLocallyConstant_of_hasCompactSupport Φ hΦ hΦc

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (RCgB.qR p)⁻¹ ^ n < δ :=
    exists_pow_lt_of_lt_one hδ (inv_lt_one_of_one_lt₀ (RCgB.one_lt_qR p))
  refine ⟨n, fun X Y hY => ?_⟩
  refine (hunif X (X + Y) ?_).symm
  rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
  refine lt_of_le_of_lt ?_ hn
  rw [inv_pow, ← zpow_natCast, ← zpow_neg]
  exact (Matrix.norm_le_iff (zpow_nonneg (RCgB.qR_pos p).le _)).2 hY

theorem exists_support_exponent (Φ : Mat → ℂ) (hΦc : HasCompactSupport Φ) :
    ∃ M : ℤ, ∀ X : Mat, Φ X ≠ 0 → ∀ i j, ‖X i j‖ ≤ RCgB.qR p ^ M := by
  letI : NormedAddCommGroup Mat := Matrix.normedAddCommGroup
  obtain ⟨R, hR⟩ := hΦc.isCompact.isBounded.subset_closedBall 0 |>.imp fun R h => h

  obtain ⟨n, hn⟩ : ∃ n : ℕ, R < RCgB.qR p ^ n := pow_unbounded_of_one_lt R (RCgB.one_lt_qR p)
  refine ⟨n, fun X hX i j => ?_⟩
  have hXs : X ∈ tsupport Φ := subset_tsupport _ (Function.mem_support.2 hX)
  have h1 : ‖X‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hXs
  rw [zpow_natCast]
  exact ((Matrix.norm_entry_le_entrywise_sup_norm X).trans h1).trans hn.le

theorem exists_bound (Φ : Mat → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ A : ℝ, ∀ X : Mat, ‖Φ X‖ ≤ A :=
  hΦ.continuous.bounded_above_of_compact_support hΦc

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}

theorem diagUnitGL2_eq_diagU (w : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    (diagUnitGL2 w : G) = RCgB.diagU p w 1 :=
  Units.ext (by rw [RCgB.coe_diagU, coe_diagUnitGL2]; simp)

theorem shell_eq (hπ : algebraMap (O) (F) ϖ ≠ 0) (n₁ n₂ : ℤ) (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (k : G) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (O) (F) ϖ) hπ ^ n₁ * u) * k =
      RCgB.diagU p (RCgB.piUnit hπ ^ n₂ * (RCgB.piUnit hπ ^ n₁ * u)) (RCgB.piUnit hπ ^ n₂) * k := by
  rw [RCgB.scalarPi_eq_diagU hπ, RCgB.diagU_zpow, diagUnitGL2_eq_diagU, RCgB.diagU_mul, mul_one]
  rfl

theorem unipotent_mul_diagU_mul_apply (x : F) (a b : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (k : G) :
    ((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) 1 0 = (b : F) * (k : Mat) 1 0 ∧
    ((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) 1 1 = (b : F) * (k : Mat) 1 1 ∧
    ((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) 0 0 = (a : F) * (k : Mat) 0 0 + x * ((b : F) * (k : Mat) 1 0) ∧
    ((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) 0 1 = (a : F) * (k : Mat) 0 1 + x * ((b : F) * (k : Mat) 1 1) := by
  have hu : ((unipotent x : G) : Mat) = !![1, x; 0, 1] := rfl
  simp only [Units.val_mul, hu, RCgB.coe_diagU, Matrix.mul_apply, Fin.sum_univ_two]
  simp

end BPhi
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport.RCgB"

namespace BPhi

open NumberField.StandardAddChar

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem unipotent_coe'' (x : F) : ((unipotent x : G) : Mat) = !![1, x; 0, 1] := rfl

theorem unipotent_mul_apply (x : F) (g : G) (j : Fin 2) :
    ((unipotent x * g : G) : Mat) 1 j = (g : Mat) 1 j ∧
    ((unipotent x * g : G) : Mat) 0 j = (g : Mat) 0 j + x * (g : Mat) 1 j := by
  simp only [Units.val_mul, unipotent_coe'', Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases j <;> simp

theorem continuous_unipotent_mul_coe (g : G) : Continuous fun x : F => ((unipotent x * g : G) : Mat) := by
  have : (fun x : F => ((unipotent x * g : G) : Mat)) = fun x => (!![(1 : F), x; 0, 1] : Mat) * (g : Mat) := by
    funext x; rw [Units.val_mul, unipotent_coe'']
  rw [this]
  refine Continuous.mul ?_ continuous_const
  refine continuous_matrix ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const] <;>
    first | exact continuous_const | exact continuous_id

theorem norm_sub_le_max' (a b : F) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max a (-b)

theorem norm_add_mul_le {a b c d : F} {B : ℝ} (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) :
    ‖a * c + b * d‖ ≤ B := by
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hc).trans ha
  · rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hd).trans hb

theorem norm_diag_le_of_kzero (x : F) (a b : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) {k : G} (hk : k ∈ RCgB.kzero p)
    {B : ℝ} (h0 : ‖((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) 0 0‖ ≤ B)
    (h1 : ‖((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) 0 1‖ ≤ B) :
    ‖(a : F)‖ ≤ B ∧ ‖x * (b : F)‖ ≤ B := by
  have hkinv := RCgB.norm_entry_le_one (inv_mem hk)
  set N : Mat := ((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) with hN
  have hprod : N * ((k⁻¹ : G) : Mat) = ((unipotent x * RCgB.diagU p a b : G) : Mat) := by
    rw [hN, ← Units.val_mul]; congr 1; group
  have hval : ((unipotent x * RCgB.diagU p a b : G) : Mat) = !![(a : F), x * (b : F); 0, (b : F)] := by
    rw [Units.val_mul, unipotent_coe'', RCgB.coe_diagU]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e00 : (a : F) = N 0 0 * ((k⁻¹ : G) : Mat) 0 0 + N 0 1 * ((k⁻¹ : G) : Mat) 1 0 := by
    have := congrFun (congrFun hprod 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, hval] at this
    simpa using this.symm
  have e01 : x * (b : F) = N 0 0 * ((k⁻¹ : G) : Mat) 0 1 + N 0 1 * ((k⁻¹ : G) : Mat) 1 1 := by
    have := congrFun (congrFun hprod 0) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, hval] at this
    simpa using this.symm
  exact ⟨e00 ▸ norm_add_mul_le p (hkinv 0 0) (hkinv 1 0) h0 h1, e01 ▸ norm_add_mul_le p (hkinv 0 1) (hkinv 1 1) h0 h1⟩

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}

theorem norm_piUnit_zpow (hϖ : Valued.v (algebraMap (O) (F) ϖ) = WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (n : ℤ) :
    ‖((RCgB.piUnit hπ ^ n : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ = RCgB.qR p ^ (-n) := by
  rw [RCgB.coe_piUnit_zpow, RCgB.norm_uniformizer_zpow hϖ]

theorem shellZ_eq (hπ : algebraMap (O) (F) ϖ ≠ 0) (d n₂ : ℤ) (k : G) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ n₂ * diagZ (algebraMap (O) (F) ϖ) hπ d * k =
      RCgB.diagU p (RCgB.piUnit hπ ^ n₂ * RCgB.piUnit hπ ^ d) (RCgB.piUnit hπ ^ n₂) * k := by
  rw [RCgB.scalarPi_eq_diagU hπ, RCgB.diagU_zpow, RCgB.diagZ_eq_diagU hπ, RCgB.diagU_mul, mul_one]

end BPhi
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport.RCgB"

open BPhi in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    letI := localBorel ℚ p

    (∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      Integrable (fun x : (p.adicCompletion ℚ) => NumberField.StandardAddChar.psiLocal ℚ p x *
        Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) (selfDualHaarAt ℚ p)) ∧

    (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (g * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) =
        (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (g) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))) ∧

    ∃ (c M : ℤ) (C : ℝ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (n₁ n₂ : ℤ) (u : (p.adicCompletion ℚ)ˣ),
      Valued.v (u : (p.adicCompletion ℚ)) = 1 →

        (c < n₂ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (n₂ < -M →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (n₁ + n₂ < -M →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0) ∧

        (c ≤ n₁ + n₂ →
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) =
          (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (c - n₂) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))) ∧

        (‖(∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p))‖ ≤ C) := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  classical
  obtain ⟨c, hc⟩ := exists_constancy_exponent p Φ hΦ hΦc
  obtain ⟨M, hM⟩ := exists_support_exponent p Φ hΦc
  obtain ⟨A, hA⟩ := exists_bound p Φ hΦ hΦc
  have hq1 := RCgB.one_lt_qR p
  have hq0 := RCgB.qR_pos p
  have hΦcont : Continuous Φ := hΦ.continuous
  have hψc := continuous_psiLocal p
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)

  have hM' : ∀ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ), (∃ i j, RCgB.qR p ^ M < ‖X i j‖) → Φ X = 0 := by
    intro X ⟨i, j, hij⟩
    by_contra h
    exact absurd (hM X h i j) (not_le.2 hij)

  have hint : ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      Integrable (fun x : (p.adicCompletion ℚ) => NumberField.StandardAddChar.psiLocal ℚ p x *
        Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))
        (selfDualHaarAt ℚ p) := by
    intro g
    refine Continuous.integrable_of_hasCompactSupport (hψc.mul (hΦcont.comp (continuous_unipotent_mul_coe p g))) ?_

    obtain ⟨j, hj⟩ : ∃ j : Fin 2, (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j ≠ 0 := by
      by_contra h
      push_neg at h
      have hdet : (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det = 0 := by
        rw [Matrix.det_fin_two, h 0, h 1]; ring
      exact (Matrix.GeneralLinearGroup.det g).ne_zero (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet)
    set R : ℝ := max (RCgB.qR p ^ M) ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j‖ /
      ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j‖ with hR
    refine HasCompactSupport.intro (isCompact_closedBall (0 : p.adicCompletion ℚ) R) (fun x hx => ?_)
    have hxR : R < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    suffices hΦ0 : Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = 0 by
      rw [hΦ0, mul_zero]
    apply hM'
    refine ⟨0, j, ?_⟩
    rw [(unipotent_mul_apply p x g j).2]
    have hgj : 0 < ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j‖ := norm_pos_iff.2 hj
    have hx' : max (RCgB.qR p ^ M) ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j‖ <
        ‖x * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j‖ := by
      rw [norm_mul]; rw [hR, div_lt_iff₀ hgj] at hxR; exact hxR

    by_contra hle
    push_neg at hle
    have h1 : ‖x * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j‖ ≤
        max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + x * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j‖
          ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j‖ := by
      have := norm_sub_le_max' p
        ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + x * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j)
        ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j)
      rwa [add_sub_cancel_left] at this
    have h2 := h1.trans (max_le (hle.trans (le_max_left _ _)) (le_max_right _ _))
    exact absurd (lt_of_lt_of_le hx' h2) (lt_irrefl _)
  refine ⟨hint, ?_, ?_⟩

  · let U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)) :=
      { carrier := {k' | ∀ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
          Φ (X * (k' : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) = Φ X}
        one_mem' := by intro X; simp
        mul_mem' := by
          intro a b ha hb X
          rw [Units.val_mul, ← mul_assoc, hb, ha]
        inv_mem' := by
          intro a ha X
          have := ha (X * ((a⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)))
          rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one] at this
          exact this.symm }
    refine ⟨U, ?_, fun k' hk' g => ?_⟩
    ·
      apply Subgroup.isOpen_of_mem_nhds
      have hr : (0 : ℝ) < RCgB.qR p ^ (-(M + c)) := zpow_pos hq0 _
      set V : Set (GL (Fin 2) (p.adicCompletion ℚ)) :=
        {k' | ∀ i j, ‖(((k' : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) - 1) i j)‖ ≤ RCgB.qR p ^ (-(M + c))} with hV
      have hVopen : IsOpen V := by
        have : V = ⋂ i : Fin 2, ⋂ j : Fin 2,
            (fun k' : GL (Fin 2) (p.adicCompletion ℚ) => ((k' : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) - 1) i j) ⁻¹'
              Metric.closedBall 0 (RCgB.qR p ^ (-(M + c))) := by
          ext k'; simp [hV, Metric.mem_closedBall, dist_zero_right]
        rw [this]
        refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
        exact (IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage
          ((Continuous.matrix_elem (Units.continuous_val.sub continuous_const) i j))
      have h1V : (1 : GL (Fin 2) (p.adicCompletion ℚ)) ∈ V := by
        intro i j
        simp only [Units.val_one, sub_self, Matrix.zero_apply, norm_zero]
        exact le_of_lt hr
      refine Filter.mem_of_superset (Filter.inter_mem (hVopen.mem_nhds h1V)
        ((RCgB.isOpen_kzero p).mem_nhds (one_mem _))) ?_
      rintro k' ⟨hk'V, hk'K⟩ X
      show Φ (X * (k' : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) = Φ X
      by_cases hX : ∀ i j, ‖X i j‖ ≤ RCgB.qR p ^ M
      · have hsplit : X * (k' : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
            X + X * ((k' : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) - 1) := by
          rw [mul_sub, mul_one, add_sub_cancel]
        rw [hsplit]
        apply hc
        intro i j
        rw [Matrix.mul_apply, Fin.sum_univ_two]
        have hb : ∀ l, ‖X i l * ((k' : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) - 1) l j‖ ≤ RCgB.qR p ^ (-c) := by
          intro l
          rw [norm_mul]
          calc ‖X i l‖ * ‖((k' : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) - 1) l j‖
              ≤ RCgB.qR p ^ M * RCgB.qR p ^ (-(M + c)) :=
                mul_le_mul (hX i l) (hk'V l j) (norm_nonneg _) (zpow_nonneg hq0.le _)
            _ = RCgB.qR p ^ (-c) := by rw [← zpow_add₀ hq0.ne']; congr 1; ring
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hb 0) (hb 1))
      ·
        push_neg at hX
        obtain ⟨i, j, hij⟩ := hX
        have hX0 : Φ X = 0 := hM' X ⟨i, j, hij⟩
        rw [hX0]
        by_contra hne
        have hbox := hM _ hne

        have hkinv := RCgB.norm_entry_le_one (inv_mem hk'K)
        have hXeq : X = X * (k' : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((k'⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := by
          rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
        have : ‖X i j‖ ≤ RCgB.qR p ^ M := by
          rw [hXeq, Matrix.mul_apply, Fin.sum_univ_two]
          exact norm_add_mul_le p (hkinv 0 j) (hkinv 1 j) (hbox i 0) (hbox i 1)
        exact absurd hij (not_lt.2 this)
    ·
      congr 1
      funext x
      rw [← mul_assoc, Units.val_mul, hk']

  ·
    obtain ⟨t, ht1, hψt⟩ := (E3ReduceSupplyF.level_zero p).2
    have htn : ‖t‖ ≤ RCgB.qR p ^ (1 : ℤ) := (norm_le_zpow_iff p hϖ t 1).2 (by simpa using ht1)

    set Bx : Set (p.adicCompletion ℚ) := Metric.closedBall 0 (RCgB.qR p ^ (M + c)) with hBx
    have hBxc : IsCompact Bx := isCompact_closedBall _ _
    obtain ⟨Aψ, hAψ⟩ := hBxc.exists_bound_of_continuousOn hψc.continuousOn
    have hAψ0 : 0 ≤ Aψ := (norm_nonneg _).trans (hAψ 0 (by simp [hBx, le_of_lt (zpow_pos hq0 _)]))
    refine ⟨c, M, Aψ * A * (selfDualHaarAt ℚ p).real Bx, fun k hk n₁ n₂ u hu => ?_⟩
    have hun : ‖(u : p.adicCompletion ℚ)‖ = 1 := (RCgB.norm_eq_one_iff p _).2 hu

    have hexa : ∃ a : (p.adicCompletion ℚ)ˣ, a = RCgB.piUnit hπ ^ n₂ * (RCgB.piUnit hπ ^ n₁ * u) := ⟨_, rfl⟩
    have hexb : ∃ b : (p.adicCompletion ℚ)ˣ, b = RCgB.piUnit hπ ^ n₂ := ⟨_, rfl⟩
    obtain ⟨a, ha⟩ := hexa
    obtain ⟨b, hb⟩ := hexb
    have hshell := shell_eq p hπ n₁ n₂ u k
    have hna : ‖(a : p.adicCompletion ℚ)‖ = RCgB.qR p ^ (-(n₁ + n₂)) := by
      rw [ha, Units.val_mul, Units.val_mul, norm_mul, norm_mul, norm_piUnit_zpow p hϖ hπ, norm_piUnit_zpow p hϖ hπ,
        hun, mul_one, ← zpow_add₀ hq0.ne']
      congr 1; ring
    have hnb : ‖(b : p.adicCompletion ℚ)‖ = RCgB.qR p ^ (-n₂) := by rw [hb, norm_piUnit_zpow p hϖ hπ]
    have hkle := RCgB.norm_entry_le_one hk

    have hrow : ∀ x : p.adicCompletion ℚ,
        unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ *
            diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) =
          unipotent x * (RCgB.diagU p a b * k) := by
      intro x; rw [hshell, ha, hb]
    have hent := fun x => unipotent_mul_diagU_mul_apply p x a b k

    have hI : c < n₂ →
        (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ *
              diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * u) * k) : GL (Fin 2) (p.adicCompletion ℚ)) :
              Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) = 0 := by
      intro hcn
      set f : p.adicCompletion ℚ → ℂ := fun x => NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ (↑(unipotent x * (RCgB.diagU p a b * k)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
        with hf
      have hshift : ∀ y, f (y + t) = (NumberField.StandardAddChar.psiLocal ℚ p t : ℂ) * f y := by
        intro y

        set Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) :=
          !![t * ((b : p.adicCompletion ℚ) * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0),
             t * ((b : p.adicCompletion ℚ) * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1); 0, 0] with hY
        have hmat : (↑(unipotent (y + t) * (RCgB.diagU p a b * k)) :
              Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
            (↑(unipotent y * (RCgB.diagU p a b * k)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) + Y := by
          obtain ⟨a10, a11, a00, a01⟩ := hent (y + t)
          obtain ⟨b10, b11, b00, b01⟩ := hent y
          rw [Matrix.eta_fin_two (↑(unipotent (y + t) * (RCgB.diagU p a b * k)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)),
            Matrix.eta_fin_two (↑(unipotent y * (RCgB.diagU p a b * k)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)),
            a00, a01, a10, a11, b00, b01, b10, b11, hY]
          ext i j
          fin_cases i <;> fin_cases j <;> simp <;> ring
        have hsmall : ∀ i j, ‖Y i j‖ ≤ RCgB.qR p ^ (-c) := by
          have key : ∀ l, ‖t * ((b : p.adicCompletion ℚ) * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 l)‖ ≤ RCgB.qR p ^ (-c) := by
            intro l
            rw [norm_mul, norm_mul, hnb]
            calc ‖t‖ * (RCgB.qR p ^ (-n₂) * ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 l‖)
                ≤ RCgB.qR p ^ (1 : ℤ) * (RCgB.qR p ^ (-n₂) * 1) := by
                  refine mul_le_mul htn (mul_le_mul_of_nonneg_left (hkle 1 l) (zpow_nonneg hq0.le _)) ?_ (zpow_nonneg hq0.le _)
                  exact mul_nonneg (zpow_nonneg hq0.le _) (norm_nonneg _)
              _ = RCgB.qR p ^ (1 - n₂) := by rw [mul_one, ← zpow_add₀ hq0.ne']; congr 1
              _ ≤ RCgB.qR p ^ (-c) := zpow_le_zpow_right₀ hq1.le (by omega)
          intro i j
          fin_cases i <;> fin_cases j
          · simp only [hY, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]; exact key 0
          · simp only [hY, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.head_cons]; exact key 1
          · simp [hY, le_of_lt (zpow_pos hq0 _)]
          · simp [hY, le_of_lt (zpow_pos hq0 _)]
        rw [hf]
        simp only
        rw [hmat, hc _ Y hsmall, AddChar.map_add_eq_mul]
        push_cast
        ring
      have hI' : (∫ x, f x ∂(selfDualHaarAt ℚ p)) = (NumberField.StandardAddChar.psiLocal ℚ p t : ℂ) * ∫ x, f x ∂(selfDualHaarAt ℚ p) := by
        conv_lhs => rw [← integral_add_right_eq_self f t]
        simp_rw [hshift]
        exact integral_const_mul _ _
      have hzero : (∫ x, f x ∂(selfDualHaarAt ℚ p)) = 0 := by
        have h1 : (1 - (NumberField.StandardAddChar.psiLocal ℚ p t : ℂ)) * ∫ x, f x ∂(selfDualHaarAt ℚ p) = 0 := by
          rw [sub_mul, one_mul, ← hI', sub_self]
        rcases mul_eq_zero.1 h1 with h | h
        · exact absurd (sub_eq_zero.1 h).symm hψt
        · exact h
      simp_rw [hrow]
      rw [hf] at hzero
      exact hzero
    refine ⟨hI, ?_, ?_, ?_, ?_⟩

    · intro hn2
      have hvan : ∀ x : p.adicCompletion ℚ, Φ (↑(unipotent x * (RCgB.diagU p a b * k)) :
          Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = 0 := by
        intro x
        apply hM'
        obtain ⟨e10, e11, -, -⟩ := hent x
        have hmax := RCgB.max_norm_bottom_row_eq_one hk
        have hbig : RCgB.qR p ^ M < RCgB.qR p ^ (-n₂) := zpow_lt_zpow_right₀ hq1 (by omega)
        rcases le_total ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖ with h | h
        · have hk10 : ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖ = 1 := by
            rw [max_eq_left h] at hmax; exact hmax
          refine ⟨1, 0, ?_⟩
          rw [e10, norm_mul, hnb, hk10, mul_one]; exact hbig
        · have hk11 : ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ = 1 := by
            rw [max_eq_right h] at hmax; exact hmax
          refine ⟨1, 1, ?_⟩
          rw [e11, norm_mul, hnb, hk11, mul_one]; exact hbig
      simp_rw [hrow, hvan, mul_zero, integral_zero]

    · intro hn12
      have hvan : ∀ x : p.adicCompletion ℚ, Φ (↑(unipotent x * (RCgB.diagU p a b * k)) :
          Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = 0 := by
        intro x
        by_contra hne
        have hbox := hM _ hne
        have hle := (norm_diag_le_of_kzero p x a b hk (hbox 0 0) (hbox 0 1)).1
        rw [hna] at hle
        exact absurd hle (not_le.2 (zpow_lt_zpow_right₀ hq1 (by omega)))
      simp_rw [hrow, hvan, mul_zero, integral_zero]

    · intro hcn
      have hexa' : ∃ a' : (p.adicCompletion ℚ)ˣ, a' = RCgB.piUnit hπ ^ n₂ * RCgB.piUnit hπ ^ (c - n₂) := ⟨_, rfl⟩
      obtain ⟨a', ha'⟩ := hexa'
      have hna' : ‖(a' : p.adicCompletion ℚ)‖ = RCgB.qR p ^ (-c) := by
        rw [ha', Units.val_mul, norm_mul, norm_piUnit_zpow p hϖ hπ, norm_piUnit_zpow p hϖ hπ, ← zpow_add₀ hq0.ne']
        congr 1; ring
      have hshell' := shellZ_eq p hπ (c - n₂) n₂ k
      have hent' := fun x => unipotent_mul_diagU_mul_apply p x a' b k
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [hrow, hshell', ← ha', ← hb]
      congr 1

      set Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) :=
        !![((a : p.adicCompletion ℚ) - a') * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0,
           ((a : p.adicCompletion ℚ) - a') * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1; 0, 0] with hY
      have hmat : (↑(unipotent x * (RCgB.diagU p a b * k)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
          (↑(unipotent x * (RCgB.diagU p a' b * k)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) + Y := by
        obtain ⟨a10, a11, a00, a01⟩ := hent x
        obtain ⟨b10, b11, b00, b01⟩ := hent' x
        rw [Matrix.eta_fin_two (↑(unipotent x * (RCgB.diagU p a b * k)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)),
          Matrix.eta_fin_two (↑(unipotent x * (RCgB.diagU p a' b * k)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)),
          a00, a01, a10, a11, b00, b01, b10, b11, hY]
        ext i j : 1
        fin_cases i <;> fin_cases j <;> simp <;> ring
      have hdiff : ‖(a : p.adicCompletion ℚ) - a'‖ ≤ RCgB.qR p ^ (-c) := by
        refine (norm_sub_le_max' p _ _).trans (max_le ?_ (le_of_eq hna'))
        rw [hna]; exact zpow_le_zpow_right₀ hq1.le (by omega)
      have hsmall : ∀ i j, ‖Y i j‖ ≤ RCgB.qR p ^ (-c) := by
        have key : ∀ l, ‖((a : p.adicCompletion ℚ) - a') * (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 l‖ ≤ RCgB.qR p ^ (-c) := by
          intro l
          rw [norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) (hkle 0 l)).trans hdiff
        intro i j
        fin_cases i <;> fin_cases j
        · simp only [hY, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]; exact key 0
        · simp only [hY, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.head_cons]; exact key 1
        · simp [hY, le_of_lt (zpow_pos hq0 _)]
        · simp [hY, le_of_lt (zpow_pos hq0 _)]
      rw [hmat, hc _ Y hsmall]

    · by_cases hcn : c < n₂
      · rw [hI hcn, norm_zero]
        exact mul_nonneg (mul_nonneg hAψ0 hA0) ENNReal.toReal_nonneg
      push_neg at hcn
      simp_rw [hrow]

      have hsupp : ∀ x : p.adicCompletion ℚ, x ∉ Bx → NumberField.StandardAddChar.psiLocal ℚ p x *
          Φ (↑(unipotent x * (RCgB.diagU p a b * k)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = 0 := by
        intro x hx
        suffices h : Φ (↑(unipotent x * (RCgB.diagU p a b * k)) :
            Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = 0 by rw [h, mul_zero]
        by_contra hne
        have hbox := hM _ hne
        have hle := (norm_diag_le_of_kzero p x a b hk (hbox 0 0) (hbox 0 1)).2
        rw [norm_mul, hnb] at hle
        apply hx
        rw [hBx, Metric.mem_closedBall, dist_zero_right]
        have hpos : 0 < RCgB.qR p ^ (-n₂) := zpow_pos hq0 _
        calc ‖x‖ = ‖x‖ * RCgB.qR p ^ (-n₂) * RCgB.qR p ^ n₂ := by
              rw [mul_assoc, ← zpow_add₀ hq0.ne', neg_add_cancel, zpow_zero, mul_one]
          _ ≤ RCgB.qR p ^ M * RCgB.qR p ^ n₂ := mul_le_mul_of_nonneg_right hle (zpow_nonneg hq0.le _)
          _ = RCgB.qR p ^ (M + n₂) := by rw [← zpow_add₀ hq0.ne']
          _ ≤ RCgB.qR p ^ (M + c) := zpow_le_zpow_right₀ hq1.le (by omega)
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
      refine norm_setIntegral_le_of_norm_le_const hBxc.measure_lt_top (fun x hx => ?_)
      rw [norm_mul]
      exact mul_le_mul (hAψ x hx) (hA _) (norm_nonneg _) hAψ0

end
end S_LanglandsTunnell_RankinSelberg_exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport (solution)
