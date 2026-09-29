-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/f076eb71-b51f-5866-a86b-e95ab24061cd

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.Analysis.Matrix.Normed
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_psiLocal_selfDualHaarAt_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal NNReal Classical

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

private theorem _root_.E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  rw [selfDualHaarAt_eq p]
  infer_instance

p2m_export "E3ReduceSupplyF" "isAddHaarMeasure_selfDualHaarAt"
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

namespace E3cH

variable (p : HeightOneSpectrum (𝓞 ℚ))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → p.adicCompletion ℚ))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_units : SecondCountableTopology (p.adicCompletion ℚ)ˣ :=
  (Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).secondCountableTopology

theorem borelSpace_units [MeasurableSpace (p.adicCompletion ℚ)] [BorelSpace (p.adicCompletion ℚ)] :
    BorelSpace (p.adicCompletion ℚ)ˣ :=
  ⟨by
    rw [(Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := p.adicCompletion ℚ)]
    rfl⟩

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

end E3cH
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.E3cH"

noncomputable section

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
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.E3cH"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.E3cH"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.E3cH"

end RCgB
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.E3cH P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.RCgB"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.E3cH P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.RCgB"

namespace DeltaKit

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

theorem exists_uniformizer : ∃ ϖ : p.adicCompletionIntegers ℚ,
    algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0 ∧
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := p.intValuation_exists_uniformizer
  have hv : Valued.v ((π : 𝓞 ℚ) : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) p π
    have h2 : p.valuation ℚ (π : ℚ) = WithZero.exp (-1 : ℤ) := by
      rw [show (π : ℚ) = algebraMap (𝓞 ℚ) ℚ π from rfl, HeightOneSpectrum.valuation_of_algebraMap]; exact hπ
    first
      | (rw [h1]; exact h2)
      | (simp only [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
           Valued.valuedCompletion_apply, HeightOneSpectrum.adicValued_apply] at h1 ⊢
         first | exact h2 | (rw [h1]; exact h2) | simpa using h2)
  have hmem : ((π : 𝓞 ℚ) : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hv, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.2 (by norm_num)
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · intro h0
    have : Valued.v ((π : 𝓞 ℚ) : p.adicCompletion ℚ) = 0 := by
      rw [show ((π : 𝓞 ℚ) : p.adicCompletion ℚ) = 0 from h0, map_zero]
    rw [hv] at this
    exact WithZero.coe_ne_zero this
  · exact hv

theorem integral_comap_val_mulMeasure (h : (F)ˣ → ℂ) :
    letI := localBorel ℚ p
    ∫ t : (F)ˣ, h t ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
      ∫ x : F, (if hx : x ≠ 0 then h (Units.mk0 x hx) * (((modulus x : ℝ) : ℂ))⁻¹ else 0) ∂(selfDualHaarAt ℚ p) := by
  classical
  letI : MeasurableSpace F := localBorel ℚ p
  haveI : BorelSpace F := borelSpace_localBorel ℚ p
  haveI : BorelSpace (F)ˣ := E3cH.borelSpace_units p
  have hME : MeasurableEmbedding (Units.val : (F)ˣ → F) := by
    refine (Units.isEmbedding_val₀ (G₀ := F)).measurableEmbedding ?_
    have : Set.range (Units.val : (F)ˣ → F) = {x : F | x ≠ 0} := by
      ext x; exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
    rw [this]; exact isOpen_ne.measurableSet
  set g : F → ℂ := fun x => if hx : x ≠ 0 then h (Units.mk0 x hx) else 0 with hg
  have hgval : g ∘ (Units.val : (F)ˣ → F) = h := by
    funext t; simp only [Function.comp_apply, hg, dif_pos t.ne_zero]; congr 1; exact Units.ext rfl
  have hrange : Set.range (Units.val : (F)ˣ → F) = {(0 : F)}ᶜ := by
    ext x; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  set D : F → ℝ≥0∞ := fun x => ((modulus x : ℝ≥0∞))⁻¹ with hD
  have hDm : Measurable D := by
    rw [hD]
    have : Continuous fun x : F => modulus x := by
      have h1 : (fun x : F => modulus x) = fun x => ‖x‖₊ := by
        funext x; rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]
      rw [h1]; exact continuous_nnnorm
    exact (ENNReal.continuous_coe.comp this).measurable.inv

  have step1 : ∫ t : (F)ˣ, h t ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
      ∫ x : F, g x ∂(Measure.map Units.val (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by
    rw [hME.integral_map]
    exact congrArg _ (funext fun t => (congrFun hgval t).symm)
  rw [step1, MeasurableEmbedding.map_comap hME, hrange, mulMeasure,
    restrict_withDensity (measurableSet_singleton (0 : F)).compl, Measure.restrict_restrict (measurableSet_singleton (0 : F)).compl,
    Set.inter_self]
  rw [integral_withDensity_eq_integral_toReal_smul₀ (hDm.aemeasurable) ?_]
  · rw [← integral_indicator (measurableSet_singleton (0 : F)).compl]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ≠ 0
    · rw [Set.indicator_of_mem (show x ∈ ({(0 : F)}ᶜ : Set F) from hx), hg]
      simp only [dif_pos hx, hD]
      rw [ENNReal.toReal_inv, Complex.real_smul, ENNReal.coe_toReal, mul_comm]
      push_cast
      rfl
    · push_neg at hx
      subst hx
      rw [Set.indicator_of_notMem (by simp)]
      simp
  · refine (ae_restrict_iff' (measurableSet_singleton (0 : F)).compl).2 (Filter.Eventually.of_forall fun x hx => ?_)
    rw [hD]
    simp only
    rw [ENNReal.inv_lt_top, pos_iff_ne_zero, ne_eq, ENNReal.coe_eq_zero, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm,
      nnnorm_eq_zero]
    exact hx

end DeltaKit
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.E3cH P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.RCgB"

namespace DeltaKit

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

theorem window_sb_and_fourier
    (Fn : (F)ˣ → ℂ) (n₁ n₀ : ℤ) (m : ℕ)
    (hf₀ : ∀ y : (F)ˣ, WithZero.exp (-n₁) < Valued.v (y : F) ∨ Valued.v (y : F) < WithZero.exp (-n₀) → Fn y = 0)
    (hf₁ : ∀ y u : (F)ˣ, Valued.v (u : F) = 1 → Valued.v ((u : F) - 1) ≤ WithZero.exp (-(m : ℤ)) → Fn (y * u) = Fn y) :
    letI := localBorel ℚ p
    IsSchwartzBruhat (fun x : F => if hx : x ≠ 0 then Fn (Units.mk0 x hx) * (((modulus x : ℝ) : ℂ))⁻¹ else 0) ∧
    ∀ y : F, ∫ t : (F)ˣ, Fn t * NumberField.StandardAddChar.psiLocal ℚ p ((t : F) * y) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
      tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p)
        (fun x : F => if hx : x ≠ 0 then Fn (Units.mk0 x hx) * (((modulus x : ℝ) : ℂ))⁻¹ else 0) y := by
  classical
  letI : MeasurableSpace F := localBorel ℚ p
  obtain ⟨ϖ, hπ, hϖ⟩ := exists_uniformizer p
  have hq0 := RCgB.qR_pos p
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  ·
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x = 0
    · subst hx
      refine ⟨Metric.ball 0 (RCgB.qR p ^ (-n₀)), Metric.isOpen_ball, Metric.mem_ball_self (zpow_pos hq0 _), fun x' hx' => ?_⟩
      rw [dif_neg (not_not.2 rfl)]
      by_cases hx'0 : x' = 0
      · subst hx'0; rw [dif_neg (not_not.2 rfl)]
      · rw [dif_pos hx'0]
        have hv : Valued.v ((Units.mk0 x' hx'0 : (F)ˣ) : F) < WithZero.exp (-n₀) := by
          rw [Units.val_mk0]
          rw [Metric.mem_ball, dist_zero_right, ← RCgB.norm_uniformizer_zpow hϖ n₀, Valued.toNormedField.norm_lt_iff,
            RCgB.v_uniformizer_zpow hϖ] at hx'
          exact hx'
        rw [hf₀ (Units.mk0 x' hx'0) (Or.inr hv), zero_mul]
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
      set r : ℝ := ‖x‖ * RCgB.qR p ^ (-(m : ℤ)) with hr
      have hrpos : 0 < r := mul_pos hxpos (zpow_pos hq0 _)
      have hrle : r ≤ ‖x‖ := by
        rw [hr]
        have : RCgB.qR p ^ (-(m : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (RCgB.one_lt_qR p).le (by omega)
        nlinarith
      refine ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hrpos, fun x' hx' => ?_⟩
      rw [Metric.mem_ball, dist_eq_norm] at hx'
      have hlt : ‖x' - x‖ < ‖x‖ := hx'.trans_le hrle

      have hnorm : ‖x'‖ = ‖x‖ := by
        have h1 : ‖x'‖ ≤ max ‖x' - x‖ ‖x‖ := by
          have := IsUltrametricDist.norm_add_le_max (x' - x) x; rwa [sub_add_cancel] at this
        have h2 : ‖x‖ ≤ max ‖x - x'‖ ‖x'‖ := by
          have := IsUltrametricDist.norm_add_le_max (x - x') x'; rwa [sub_add_cancel] at this
        rw [norm_sub_rev] at h2
        rcases le_or_gt ‖x‖ ‖x'‖ with h | h
        · exact le_antisymm (h1.trans (max_le hlt.le le_rfl)) h
        · exact absurd (h2.trans_lt (max_lt hlt h)) (lt_irrefl _)
      have hx'0 : x' ≠ 0 := by rw [← norm_pos_iff, hnorm]; exact hxpos
      rw [dif_pos hx'0, dif_pos hx]

      set u : (F)ˣ := Units.mk0 x' hx'0 * (Units.mk0 x hx)⁻¹ with hu
      have hucoe : (u : F) = x' * x⁻¹ := by rw [hu]; simp
      have hvu : Valued.v (u : F) = 1 := by
        rw [← RCgB.norm_eq_one_iff p, hucoe, norm_mul, norm_inv, hnorm, mul_inv_cancel₀ hxpos.ne']
      have hvu1 : Valued.v ((u : F) - 1) ≤ WithZero.exp (-(m : ℤ)) := by
        rw [← BPhi.norm_le_zpow_iff p hϖ, hucoe]
        have : x' * x⁻¹ - 1 = (x' - x) * x⁻¹ := by field_simp
        rw [this, norm_mul, norm_inv]
        rw [hr] at hx'
        rw [mul_inv_le_iff₀ hxpos, mul_comm]; exact hx'.le
      have hmk : Units.mk0 x' hx'0 = Units.mk0 x hx * u := by rw [hu, mul_left_comm, mul_inv_cancel, mul_one]
      rw [hmk, hf₁ _ u hvu hvu1]
      congr 2
      rw [RCgB.coe_modulus_eq_norm, RCgB.coe_modulus_eq_norm, hnorm]
  ·
    refine HasCompactSupport.intro' (isCompact_closedBall (0 : F) (RCgB.qR p ^ (-n₁))) Metric.isClosed_closedBall fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    have hx0 : x ≠ 0 := norm_pos_iff.1 ((zpow_pos hq0 _).trans hx)
    rw [dif_pos hx0]
    have hv : WithZero.exp (-n₁) < Valued.v ((Units.mk0 x hx0 : (F)ˣ) : F) := by
      rw [Units.val_mk0]
      rw [← RCgB.norm_uniformizer_zpow hϖ n₁, Valued.toNormedField.norm_lt_iff, RCgB.v_uniformizer_zpow hϖ] at hx
      exact hx
    rw [hf₀ (Units.mk0 x hx0) (Or.inl hv), zero_mul]
  ·
    rw [integral_comap_val_mulMeasure, tateFourier]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    by_cases hx : x ≠ 0
    · rw [dif_pos hx, dif_pos hx, Units.val_mk0]; ring
    · rw [dif_neg hx, dif_neg hx, zero_mul]

end DeltaKit
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.E3cH P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.RCgB"

open DeltaKit in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Fn : (p.adicCompletion ℚ)ˣ → ℂ) (n₁ n₀ : ℤ) (m : ℕ)
    (hf₀ : ∀ y : (p.adicCompletion ℚ)ˣ,
      WithZero.exp (-n₁) < Valued.v (y : p.adicCompletion ℚ) ∨ Valued.v (y : p.adicCompletion ℚ) < WithZero.exp (-n₀) →
        Fn y = 0)
    (hf₁ : ∀ y u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(m : ℤ)) → Fn (y * u) = Fn y)
    (b : (p.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ p
    Integrable (fun y : p.adicCompletion ℚ =>
        ∫ t : (p.adicCompletion ℚ)ˣ, Fn t * NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ) * y)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) (selfDualHaarAt ℚ p) ∧
    (∫ y : p.adicCompletion ℚ,
        (∫ t : (p.adicCompletion ℚ)ˣ, Fn t * NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ) * y)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
        NumberField.StandardAddChar.psiLocal ℚ p ((b : p.adicCompletion ℚ) * y) ∂(selfDualHaarAt ℚ p)) =
      (((modulus (b : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹ * Fn (-b) ∧
    (∫ y : p.adicCompletion ℚ,
        (∫ t : (p.adicCompletion ℚ)ˣ, Fn t * NumberField.StandardAddChar.psiLocal ℚ p (-((t : p.adicCompletion ℚ) * y))
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
        NumberField.StandardAddChar.psiLocal ℚ p (-((b : p.adicCompletion ℚ) * y)) ∂(selfDualHaarAt ℚ p)) =
      (((modulus (b : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹ * Fn (-b) := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  classical
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ)ˣ := E3cH.borelSpace_units p
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3cH.isAddHaarMeasure_selfDualHaarAt p
  haveI hτH : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (p.adicCompletion ℚ)ˣ).IsHaarMeasure :=
    LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)
  obtain ⟨h0, h1⟩ := E3ReduceSupplyF.level_zero p
  have hψc := BPhi.continuous_psiLocal p

  obtain ⟨hG, hFou⟩ := window_sb_and_fourier p Fn n₁ n₀ m hf₀ hf₁
  have hf₀' : ∀ y : (p.adicCompletion ℚ)ˣ, WithZero.exp (-n₁) < Valued.v (y : p.adicCompletion ℚ) ∨
      Valued.v (y : p.adicCompletion ℚ) < WithZero.exp (-n₀) → (fun t => Fn (-t)) y = 0 := by
    intro y hy
    simp only
    apply hf₀
    rwa [Units.val_neg, Valuation.map_neg]
  have hf₁' : ∀ y u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(m : ℤ)) → (fun t => Fn (-t)) (y * u) = (fun t => Fn (-t)) y := by
    intro y u hu hu1
    simp only
    rw [← neg_mul]
    exact hf₁ _ u hu hu1
  obtain ⟨hG', hFou'⟩ := window_sb_and_fourier p (fun t => Fn (-t)) n₁ n₀ m hf₀' hf₁'
  set G : p.adicCompletion ℚ → ℂ := fun x => if hx : x ≠ 0 then Fn (Units.mk0 x hx) * (((modulus x : ℝ) : ℂ))⁻¹ else 0 with hGdef
  set G' : p.adicCompletion ℚ → ℂ := fun x => if hx : x ≠ 0 then (fun t => Fn (-t)) (Units.mk0 x hx) * (((modulus x : ℝ) : ℂ))⁻¹ else 0 with hG'def
  have hFG : IsSchwartzBruhat (tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) G) :=
    LanglandsTunnell.TateLocal.isSchwartzBruhat_tateFourier ℚ p (selfDualHaarAt ℚ p) _ 0 h0 h1 G hG

  have hGb : G (-(b : p.adicCompletion ℚ)) = (((modulus (b : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹ * Fn (-b) := by
    rw [hGdef]
    simp only
    rw [dif_pos (neg_ne_zero.2 b.ne_zero)]
    have : Units.mk0 (-(b : p.adicCompletion ℚ)) (neg_ne_zero.2 b.ne_zero) = -b := Units.ext (by simp)
    rw [this, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm,
      nnnorm_neg, mul_comm]
  have hG'b : G' (b : p.adicCompletion ℚ) = (((modulus (b : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹ * Fn (-b) := by
    rw [hG'def]
    simp only
    rw [dif_pos b.ne_zero]
    have : Units.mk0 (b : p.adicCompletion ℚ) b.ne_zero = b := Units.ext (by simp)
    rw [this, mul_comm]
  refine ⟨?_, ?_, ?_⟩
  ·
    have : (fun y : p.adicCompletion ℚ => ∫ t : (p.adicCompletion ℚ)ˣ, Fn t *
        NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ) * y) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) G := funext hFou
    rw [this]
    exact hFG.1.continuous.integrable_of_hasCompactSupport hFG.2
  ·
    simp_rw [hFou]
    have := LanglandsTunnell.TateLocal.tateFourier_tateFourier_psiLocal_selfDualHaarAt_rat p G hG (b : p.adicCompletion ℚ)
    rw [tateFourier] at this
    rw [← hGb, ← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [mul_comm y (b : p.adicCompletion ℚ)]
  ·
    have hinner : ∀ y : p.adicCompletion ℚ,
        ∫ t : (p.adicCompletion ℚ)ˣ, Fn t * NumberField.StandardAddChar.psiLocal ℚ p (-((t : p.adicCompletion ℚ) * y))
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
        tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) G' y := by
      intro y
      rw [← hFou' y]
      have := integral_mul_left_eq_self (μ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        (fun t : (p.adicCompletion ℚ)ˣ => Fn (-t) * NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ) * y)) (-1)
      rw [← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [neg_mul, one_mul, neg_neg, Units.val_neg]
    simp_rw [hinner]
    have := LanglandsTunnell.TateLocal.tateFourier_tateFourier_psiLocal_selfDualHaarAt_rat p G' hG' (-(b : p.adicCompletion ℚ))
    rw [tateFourier, neg_neg] at this
    rw [← hG'b, ← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [mul_neg, mul_comm y (b : p.adicCompletion ℚ)]

end
end
end S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window (solution)
