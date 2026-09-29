-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetIntegral_spherical_laws_of_unramified_of_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3c420ae8-c629-5d75-a6e4-07c0b177af51

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetIntegral_spherical_laws_of_unramified_of_norm_lt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm UnramifiedWhittaker Filter Topology Matrix

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace KcSphJacquetRekey

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Γ" => (WithZero (Multiplicative ℤ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

def qR : ℝ := ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)

def sR : ℝ := Real.sqrt (qR p)

theorem one_lt_qR : (1 : ℝ) < qR p := by
  unfold qR; exact_mod_cast HeightOneSpectrum.one_lt_absNorm p

theorem qR_pos : (0 : ℝ) < qR p := lt_trans one_pos (one_lt_qR p)

theorem sR_pos : (0 : ℝ) < sR p := Real.sqrt_pos.mpr (qR_pos p)

theorem sR_sq : sR p ^ 2 = qR p := Real.sq_sqrt (qR_pos p).le

theorem sC_ne_zero : ((sR p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sR_pos p).ne'

theorem qC_eq : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) = ((qR p : ℝ) : ℂ) := by unfold qR; push_cast; rfl

theorem qC_eq_sC_sq : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) = ((sR p : ℝ) : ℂ) ^ 2 := by
  rw [qC_eq, ← Complex.ofReal_pow, sR_sq]

theorem qC_ne_zero : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ≠ 0 := by
  rw [qC_eq_sC_sq]; exact pow_ne_zero 2 (sC_ne_zero p)

theorem qC_cpow_neg_half : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-(1 / 2 : ℂ)) = (((sR p : ℝ) : ℂ))⁻¹ := by
  rw [qC_eq, show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (qR_pos p).le, ← Complex.ofReal_inv]
  congr 1
  rw [Real.rpow_neg (qR_pos p).le, sR, Real.sqrt_eq_rpow]

def lv (y : F) : ℤ := WithZero.log (Valued.v y)

theorem v_ne_zero {y : F} (hy : y ≠ 0) : (Valued.v y : Γ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hy

theorem exp_lv {y : F} (hy : y ≠ 0) : WithZero.exp (lv p y) = Valued.v y := WithZero.exp_log (v_ne_zero p hy)

theorem lv_of_v_eq {y : F} {k : ℤ} (h : Valued.v y = WithZero.exp k) : lv p y = k := by
  rw [lv, h, WithZero.log_exp]

theorem lv_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) : lv p (x * y) = lv p x + lv p y := by
  rw [lv, map_mul, WithZero.log_mul (v_ne_zero p hx) (v_ne_zero p hy)]; rfl

private theorem toAdd_unzero_exp (n : ℤ) (h : (WithZero.exp n : Γ) ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero h) = n :=
  rfl

theorem norm_eq_zpow_of_valued {y : F} {k : ℤ} (h : Valued.v y = WithZero.exp k) : ‖y‖ = qR p ^ k := by
  rw [NumberField.FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    toAdd_unzero_exp]
  unfold qR
  push_cast
  rfl

theorem norm_eq_zpow_lv {y : F} (hy : y ≠ 0) : ‖y‖ = qR p ^ lv p y :=
  norm_eq_zpow_of_valued p (exp_lv p hy).symm

theorem norm_units_eq (a : Fˣ) : ‖(a : F)‖ = sR p ^ (2 * lv p (a : F)) := by
  rw [norm_eq_zpow_lv p a.ne_zero, _root_.zpow_mul, ← sR_sq]
  norm_cast

abbrev kzero : Subgroup G := AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤

variable {p}

theorem v_entry_le_one {k : G} (hk : k ∈ kzero p) (i j : Fin 2) : Valued.v ((k : Mat) i j) ≤ 1 := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk.1.integral i j)

theorem v_det_le_one_of_integral {m : Mat} (h : ∀ i j, Valued.v (m i j) ≤ 1) : Valued.v m.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  calc Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0)
      ≤ max (Valued.v (m 0 0 * m 1 1)) (Valued.v (m 0 1 * m 1 0)) := Valuation.map_sub _ _ _
    _ ≤ 1 := by
        refine max_le ?_ ?_
        · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
        · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

theorem v_det_eq_one {k : G} (hk : k ∈ kzero p) : Valued.v (k : Mat).det = 1 := by
  have h1 : Valued.v (k : Mat).det ≤ 1 := v_det_le_one_of_integral (v_entry_le_one hk)
  have h2 : Valued.v ((k⁻¹ : G) : Mat).det ≤ 1 := v_det_le_one_of_integral (v_entry_le_one (inv_mem hk))
  have hprod : Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : Γ) = Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det := hprod.symm
    _ ≤ Valued.v (k : Mat).det * 1 := by gcongr
    _ = Valued.v (k : Mat).det := mul_one _

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ HeightOneSpectrum.adicCompletionIntegers ℚ p) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_of_integral {k : G} (h : ∀ i j, Valued.v ((k : Mat) i j) ≤ 1)
    (h' : ∀ i j, Valued.v (((k⁻¹ : G) : Mat) i j) ≤ 1) : k ∈ kzero p := by
  rw [AdelicDock.mem_localLevelOne_iff]
  exact ⟨isLocalLevelOne_top_of_integral fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h i j),
    isLocalLevelOne_top_of_integral fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h' i j)⟩

theorem coe_kzero_eq_localIntegralSet : ((kzero p : Subgroup G) : Set G) = AutomorphicForm.localIntegralSet ℚ p := by
  ext k
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff, AutomorphicForm.mem_localIntegralSet]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩; exact ⟨isLocalLevelOne_top_of_integral h1, isLocalLevelOne_top_of_integral h2⟩

theorem isOpen_kzero : IsOpen ((kzero p : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact AutomorphicForm.isOpen_localIntegralSet ℚ p

theorem unipotentGL2_mem_kzero {x : F} (hx : Valued.v x ≤ 1) : (unipotentGL2 x : G) ∈ kzero p := by
  have hinv : ((unipotentGL2 x : G)⁻¹) = unipotentGL2 (-x) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]
  refine mem_kzero_of_integral (fun i j => ?_) (fun i j => ?_)
  · rw [unipotentGL2_coe]; fin_cases i <;> fin_cases j <;> simp [hx]
  · rw [hinv, unipotentGL2_coe]; fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, hx]

variable (p)

def rowV (g : G) : Γ := max (Valued.v ((g : Mat) 1 0)) (Valued.v ((g : Mat) 1 1))

theorem det_ne_zero (g : G) : (g : Mat).det ≠ 0 := by
  have h := (Matrix.GeneralLinearGroup.det g).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h

theorem rowV_ne_zero (g : G) : rowV p g ≠ 0 := by
  intro h
  have h0 : Valued.v ((g : Mat) 1 0) = 0 := le_antisymm (h ▸ le_max_left _ _) zero_le'
  have h1 : Valued.v ((g : Mat) 1 1) = 0 := le_antisymm (h ▸ le_max_right _ _) zero_le'
  rw [Valuation.zero_iff] at h0 h1
  apply det_ne_zero p g
  rw [Matrix.det_fin_two, h0, h1]; ring

variable {p}

theorem rowV_mul_le {k : G} (hk : k ∈ kzero p) (g : G) : rowV p (g * k) ≤ rowV p g := by
  have hent : ∀ j : Fin 2, Valued.v (((g * k : G) : Mat) 1 j) ≤ rowV p g := by
    intro j
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    calc Valued.v ((g : Mat) 1 0 * (k : Mat) 0 j + (g : Mat) 1 1 * (k : Mat) 1 j)
        ≤ max (Valued.v ((g : Mat) 1 0 * (k : Mat) 0 j)) (Valued.v ((g : Mat) 1 1 * (k : Mat) 1 j)) :=
          Valuation.map_add _ _ _
      _ ≤ max (Valued.v ((g : Mat) 1 0)) (Valued.v ((g : Mat) 1 1)) := by
          rw [map_mul, map_mul]
          exact max_le_max (mul_le_of_le_one_right' (v_entry_le_one hk 0 j))
            (mul_le_of_le_one_right' (v_entry_le_one hk 1 j))
  exact max_le (hent 0) (hent 1)

theorem rowV_mul {k : G} (hk : k ∈ kzero p) (g : G) : rowV p (g * k) = rowV p g := by
  refine le_antisymm (rowV_mul_le hk g) ?_
  have := rowV_mul_le (inv_mem hk) (g * k)
  rwa [mul_inv_cancel_right] at this

theorem v_det_mul {k : G} (hk : k ∈ kzero p) (g : G) : Valued.v ((g * k : G) : Mat).det = Valued.v (g : Mat).det := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, v_det_eq_one hk, mul_one]

theorem rowV_one : rowV p (1 : G) = 1 := by
  simp [rowV]

theorem rowV_upperUnipotent2_mul (x : F) (g : G) : rowV p (upperUnipotent2 p x * g) = rowV p g := by
  have h10 := gl2Entry_upperUnipotent2_mul_one p x g 0
  have h11 := gl2Entry_upperUnipotent2_mul_one p x g 1
  simp only [gl2Entry] at h10 h11
  rw [rowV, rowV, h10, h11]

theorem rowV_diagonal2_mul (a : Fin 2 → Fˣ) (g : G) :
    rowV p (diagonal2 p a * g) = Valued.v (a 1 : F) * rowV p g := by
  have h10 := gl2Entry_diagonal2_mul p a g 1 0
  have h11 := gl2Entry_diagonal2_mul p a g 1 1
  simp only [gl2Entry] at h10 h11
  rw [rowV, rowV, h10, h11, map_mul, map_mul]
  rcases le_total (Valued.v ((g : Mat) 1 0)) (Valued.v ((g : Mat) 1 1)) with h | h
  · rw [max_eq_right h, max_eq_right (mul_le_mul_right h _)]
  · rw [max_eq_left h, max_eq_left (mul_le_mul_right h _)]

variable (p)

def unrChar (z : ℂˣ) : Fˣ →* ℂˣ where
  toFun a := z ^ (-lv p (a : F))
  map_one' := by simp [lv]
  map_mul' a b := by
    rw [Units.val_mul, lv_mul p a.ne_zero b.ne_zero, neg_add, _root_.zpow_add]

theorem unrChar_apply (z : ℂˣ) (a : Fˣ) : ((unrChar p z a : ℂˣ) : ℂ) = (z : ℂ) ^ (-lv p (a : F)) := by
  simp [unrChar]

theorem unrChar_unram (z : ℂˣ) (u : Fˣ) (hu : u ∈ higherUnitsAt ℚ p 0) : unrChar p z u = 1 := by
  rw [mem_higherUnitsAt_zero_iff] at hu
  have : lv p (u : F) = 0 := by rw [lv, hu, WithZero.log_one]
  simp [unrChar, this]

theorem unrChar_uniformizer (z : ℂˣ) (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) :
    ((unrChar p z ϖ : ℂˣ) : ℂ) = (z : ℂ) := by
  rw [unrChar_apply, lv_of_v_eq p hϖ, neg_neg, zpow_one]

def muV (g : G) : ℤ := WithZero.log (rowV p g)

def lamV (g : G) : ℤ := lv p (g : Mat).det

def sph (z₀ z₁ : ℂ) (g : G) : ℂ :=
  z₀ ^ (muV p g - lamV p g) * z₁ ^ (-muV p g) * ((sR p : ℝ) : ℂ) ^ (lamV p g - 2 * muV p g)

variable {p}

theorem muV_mul {k : G} (hk : k ∈ kzero p) (g : G) : muV p (g * k) = muV p g := by
  rw [muV, muV, rowV_mul hk]

theorem lamV_mul {k : G} (hk : k ∈ kzero p) (g : G) : lamV p (g * k) = lamV p g := by
  rw [lamV, lamV, lv, lv, v_det_mul hk]

theorem sph_mul (z₀ z₁ : ℂ) {k : G} (hk : k ∈ kzero p) (g : G) : sph p z₀ z₁ (g * k) = sph p z₀ z₁ g := by
  rw [sph, sph, muV_mul hk, lamV_mul hk]

theorem muV_one : muV p (1 : G) = 0 := by
  rw [muV, rowV_one, WithZero.log_one]

theorem lamV_one : lamV p (1 : G) = 0 := by
  rw [lamV, lv, Units.val_one, Matrix.det_one, map_one, WithZero.log_one]

theorem sph_one (z₀ z₁ : ℂ) : sph p z₀ z₁ (1 : G) = 1 := by
  rw [sph, muV_one, lamV_one]; simp

theorem muV_upperUnipotent2_mul (x : F) (g : G) : muV p (upperUnipotent2 p x * g) = muV p g := by
  rw [muV, muV, rowV_upperUnipotent2_mul]

theorem lamV_upperUnipotent2_mul (x : F) (g : G) : lamV p (upperUnipotent2 p x * g) = lamV p g := by
  have h := gl2Det_upperUnipotent2_mul p x g
  simp only [gl2Det] at h
  rw [lamV, lamV, h]

theorem muV_diagonal2_mul (a : Fin 2 → Fˣ) (g : G) : muV p (diagonal2 p a * g) = lv p (a 1 : F) + muV p g := by
  rw [muV, muV, rowV_diagonal2_mul, WithZero.log_mul (v_ne_zero p (a 1).ne_zero) (rowV_ne_zero p g), lv]

theorem lamV_diagonal2_mul (a : Fin 2 → Fˣ) (g : G) :
    lamV p (diagonal2 p a * g) = lv p (a 0 : F) + lv p (a 1 : F) + lamV p g := by
  have h := gl2Det_diagonal2_mul p a g
  simp only [gl2Det] at h
  rw [lamV, lamV, h, lv_mul p (mul_ne_zero (a 0).ne_zero (a 1).ne_zero) (det_ne_zero p g),
    lv_mul p (a 0).ne_zero (a 1).ne_zero]

theorem halfModulus2_eq (a : Fin 2 → Fˣ) :
    halfModulus2 p a = ((sR p : ℝ) : ℂ) ^ (lv p (a 0 : F) - lv p (a 1 : F)) := by
  unfold halfModulus2
  rw [norm_units_eq p (a 0), norm_units_eq p (a 1), ← zpow_sub₀ (sR_pos p).ne', ← mul_sub, mul_comm,
    _root_.zpow_mul, show (sR p ^ (lv p (a 0 : F) - lv p (a 1 : F))) ^ (2 : ℤ) =
      (sR p ^ (lv p (a 0 : F) - lv p (a 1 : F))) ^ 2 from zpow_ofNat _ 2,
    Real.sqrt_sq (zpow_nonneg (sR_pos p).le _)]
  push_cast
  rfl

theorem sph_diagonal2_mul (z₀ z₁ : ℂˣ) (a : Fin 2 → Fˣ) (g : G) :
    sph p z₀ z₁ (diagonal2 p a * g) =
      torusChar2 p ![unrChar p z₀, unrChar p z₁] a * halfModulus2 p a * sph p z₀ z₁ g := by
  have hs := sC_ne_zero p
  have h0 : ((z₀ : ℂˣ) : ℂ) ≠ 0 := z₀.ne_zero
  have h1 : ((z₁ : ℂˣ) : ℂ) ≠ 0 := z₁.ne_zero
  rw [sph, sph, muV_diagonal2_mul, lamV_diagonal2_mul, halfModulus2_eq]
  simp only [torusChar2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, unrChar_apply]
  set l0 := lv p (a 0 : F)
  set l1 := lv p (a 1 : F)
  set μ := muV p g
  set la := lamV p g
  rw [show l1 + μ - (l0 + l1 + la) = -l0 + (μ - la) by ring, zpow_add₀ h0,
    show -(l1 + μ) = -l1 + -μ by ring, zpow_add₀ h1,
    show l0 + l1 + la - 2 * (l1 + μ) = (l0 - l1) + (la - 2 * μ) by ring, zpow_add₀ hs]
  ring

theorem sph_upperUnipotent2_mul (z₀ z₁ : ℂ) (x : F) (g : G) :
    sph p z₀ z₁ (upperUnipotent2 p x * g) = sph p z₀ z₁ g := by
  rw [sph, sph, muV_upperUnipotent2_mul, lamV_upperUnipotent2_mul]

theorem isLocallyConstant_sph (z₀ z₁ : ℂ) : IsLocallyConstant (sph p z₀ z₁) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun x => ?_
  refine ⟨(fun h => x⁻¹ * h) ⁻¹' ((kzero p : Subgroup G) : Set G),
    (isOpen_kzero).preimage (continuous_const.mul continuous_id), by simp, fun y hy => ?_⟩
  have := sph_mul z₀ z₁ hy x
  rwa [mul_inv_cancel_left] at this

theorem sph_mem (z₀ z₁ : ℂˣ) : sph p z₀ z₁ ∈ principalSeries2 p ![unrChar p z₀, unrChar p z₁] :=
  mem_principalSeries2_iff.mpr
    ⟨isLocallyConstant_sph _ _, sph_upperUnipotent2_mul _ _, sph_diagonal2_mul z₀ z₁⟩

section Values

variable (p)
variable (π : HeightOneSpectrum.adicCompletion ℚ p) (hπ : π ≠ 0) (hvπ : Valued.v π = WithZero.exp (-1 : ℤ))

theorem coe_weyl_unip_diagZ (m : ℤ) (y : F) :
    ((antidiagonal2 p * unipotentGL2 y * diagZ π hπ m : G) : Mat) = !![0, 1; π ^ m, y] := by
  rw [Units.val_mul, Units.val_mul, antidiagonal2_coe, unipotentGL2_coe]
  rw [show ((diagZ π hπ m : G) : Mat) = !![π ^ m, 0; 0, 1] from rfl]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

include hvπ in
theorem v_pi_zpow (m : ℤ) : Valued.v (π ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hvπ, ← WithZero.exp_zsmul]
  congr 1
  simp

include hvπ in
theorem rowV_weyl (m : ℤ) (y : F) :
    rowV p (antidiagonal2 p * unipotentGL2 y * diagZ π hπ m) = max (WithZero.exp (-m)) (Valued.v y) := by
  rw [rowV, coe_weyl_unip_diagZ]
  simp [v_pi_zpow p π hvπ]

include hvπ in
theorem lamV_weyl (m : ℤ) (y : F) : lamV p (antidiagonal2 p * unipotentGL2 y * diagZ π hπ m) = -m := by
  rw [lamV, coe_weyl_unip_diagZ, Matrix.det_fin_two_of]
  apply lv_of_v_eq
  rw [show (0 : F) * y - 1 * π ^ m = -(π ^ m) by ring, Valuation.map_neg, v_pi_zpow p π hvπ]

include hvπ in

theorem sph_weyl (z₀ z₁ : ℂ) (m : ℤ) (y : F) :
    sph p z₀ z₁ (antidiagonal2 p * unipotentGL2 y * diagZ π hπ m) =
      z₀ ^ (WithZero.log (max (WithZero.exp (-m)) (Valued.v y)) + m) *
        z₁ ^ (-WithZero.log (max (WithZero.exp (-m)) (Valued.v y))) *
        ((sR p : ℝ) : ℂ) ^ (-m - 2 * WithZero.log (max (WithZero.exp (-m)) (Valued.v y))) := by
  rw [sph, muV, rowV_weyl p π hπ hvπ, lamV_weyl p π hπ hvπ]
  congr 2 <;> ring

include hvπ in

theorem sph_weyl_small (z₀ z₁ : ℂ) (m : ℤ) {y : F} (hy : Valued.v y ≤ WithZero.exp (-m)) :
    sph p z₀ z₁ (antidiagonal2 p * unipotentGL2 y * diagZ π hπ m) = z₁ ^ m * ((sR p : ℝ) : ℂ) ^ m := by
  rw [sph_weyl p π hπ hvπ, max_eq_left hy, WithZero.log_exp]
  simp only [neg_add_cancel, zpow_zero, one_mul, neg_neg]
  congr 1
  ring

include hvπ in

theorem sph_weyl_shell (z₀ z₁ : ℂ) (m j : ℤ) (hj : -m < j) {y : F} (hy : Valued.v y = WithZero.exp j) :
    sph p z₀ z₁ (antidiagonal2 p * unipotentGL2 y * diagZ π hπ m) =
      z₀ ^ (j + m) * z₁ ^ (-j) * ((sR p : ℝ) : ℂ) ^ (-m - 2 * j) := by
  rw [sph_weyl p π hπ hvπ, hy, max_eq_right (WithZero.exp_le_exp.mpr hj.le), WithZero.log_exp]

include hvπ in

theorem sph_weyl_congr (z₀ z₁ : ℂ) (m : ℤ) {y y' : F} (h : Valued.v y = Valued.v y') :
    sph p z₀ z₁ (antidiagonal2 p * unipotentGL2 y * diagZ π hπ m) =
      sph p z₀ z₁ (antidiagonal2 p * unipotentGL2 y' * diagZ π hπ m) := by
  rw [sph_weyl p π hπ hvπ, sph_weyl p π hπ hvπ, h]

end Values

variable (p)

def ball (k : ℤ) : Set F := {y | Valued.v y ≤ WithZero.exp k}

variable {p}

theorem mem_ball {k : ℤ} {y : F} : y ∈ ball p k ↔ Valued.v y ≤ WithZero.exp k := Iff.rfl

theorem valued_units_zpow (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (((ϖ ^ k : Fˣ) : F)) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  ring

theorem ball_eq_setOf_le_valued {k : ℤ} {t : F} (hvt : Valued.v t = WithZero.exp k) :
    ball p k = {y : F | Valued.v y ≤ Valued.v t} := by
  rw [hvt]; rfl

theorem isClosed_ball' {k : ℤ} {t : F} (ht : t ≠ 0) (hvt : Valued.v t = WithZero.exp k) : IsClosed (ball p k) := by
  rw [ball_eq_setOf_le_valued hvt]
  exact AdelicLevel.isClosed_setOf_valued_le p t ht

theorem measurableSet_ball {k : ℤ} {t : F} (ht : t ≠ 0) (hvt : Valued.v t = WithZero.exp k) :
    MeasurableSet (ball p k) :=
  (isClosed_ball' ht hvt).measurableSet

theorem ball_eq_smul {k : ℤ} (t : Fˣ) (hvt : Valued.v (t : F) = WithZero.exp k) :
    ball p k = t • ((HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F)) := by
  ext y
  rw [mem_ball, Set.mem_smul_set]
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro hy
    refine ⟨(t⁻¹ : Fˣ) • y, ?_, by simp⟩
    rw [Units.smul_def, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvt]
    calc (WithZero.exp k)⁻¹ * Valued.v y ≤ (WithZero.exp k)⁻¹ * WithZero.exp k := mul_le_mul_right hy _
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
  · rintro ⟨z, hz, rfl⟩
    rw [Units.smul_def, smul_eq_mul, map_mul, hvt]
    calc WithZero.exp k * Valued.v z ≤ WithZero.exp k * 1 := mul_le_mul_right hz _
      _ = WithZero.exp k := mul_one _

theorem isCompact_ball {k : ℤ} (t : Fˣ) (hvt : Valued.v (t : F) = WithZero.exp k) : IsCompact (ball p k) := by
  rw [ball_eq_smul t hvt, ← coe_integersPositiveCompacts ℚ p]
  exact (integersPositiveCompacts ℚ p).isCompact.smul _

theorem ball_zero_eq : ball p 0 = (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) := by
  ext y
  rw [mem_ball, WithZero.exp_zero, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem measureReal_ball (ϖ : Fˣ) (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ))
    (ν : Measure F) [ν.IsAddHaarMeasure] (m : ℤ) :
    ν.real (ball p m) = qR p ^ m * ν.real (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) := by
  have hv : Valued.v (((ϖ ^ (-m) : Fˣ) : F)) = WithZero.exp m := by rw [valued_units_zpow ϖ hϖ, neg_neg]
  rw [ball_eq_smul (ϖ ^ (-m)) hv, Measure.real,
    ← MeasureTheory.distribHaarChar_mul ν (ϖ ^ (-m)) (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F),
    ← modulus_coe_units,
    LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, ENNReal.toReal_mul, Measure.real]
  congr 1
  rw [ENNReal.coe_toReal, coe_nnnorm, norm_eq_zpow_of_valued p hv]

theorem measureReal_integers_pos (ν : Measure F) [ν.IsAddHaarMeasure] :
    0 < ν.real (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) := by
  rw [← coe_integersPositiveCompacts ℚ p]
  refine ENNReal.toReal_pos ?_ (integersPositiveCompacts ℚ p).isCompact.measure_lt_top.ne
  exact ((isOpen_interior.measure_pos ν (integersPositiveCompacts ℚ p).interior_nonempty).trans_le
    (measure_mono interior_subset)).ne'

theorem add_mem_ball_iff {k : ℤ} {t : F} (ht : Valued.v t ≤ WithZero.exp k) (y : F) :
    y + t ∈ ball p k ↔ y ∈ ball p k := by
  constructor
  · intro h
    have : y = (y + t) + (-t) := by ring
    rw [mem_ball, this]
    exact (Valuation.map_add _ _ _).trans (max_le h (by rwa [Valuation.map_neg]))
  · intro h
    exact (Valuation.map_add _ _ _).trans (max_le h ht)

section Theta

theorem continuous_theta (θ : AddChar F ℂ) (hθ0 : ∀ x : F, Valued.v x ≤ 1 → θ x = 1) :
    Continuous (fun x : F => θ x) := by
  refine continuous_iff_continuousAt.mpr fun a => ?_
  have hev : ∀ᶠ b : F in 𝓝 a, θ b = θ a := by
    have hopen : IsOpen {y : F | Valued.v y ≤ Valued.v (1 : F)} := AdelicLevel.isOpen_setOf_valued_le p 1 one_ne_zero
    have hmem : (fun u => a + u) '' {y : F | Valued.v y ≤ Valued.v (1 : F)} ∈ 𝓝 a :=
      ((Homeomorph.addLeft a).isOpenMap _ hopen).mem_nhds ⟨0, by simp, by simp⟩
    filter_upwards [hmem] with b hb
    obtain ⟨u, hu, rfl⟩ := hb
    rw [Set.mem_setOf_eq, map_one] at hu
    rw [AddChar.map_add_eq_mul, hθ0 u hu, mul_one]
  exact continuousAt_const.congr (Filter.EventuallyEq.symm hev)

theorem theta_ball_zero (θ : AddChar F ℂ) (hθ0 : ∀ x : F, Valued.v x ≤ 1 → θ x = 1) {y : F} (hy : y ∈ ball p 0) :
    θ y = 1 := by
  apply hθ0
  rw [ball_zero_eq] at hy
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hy

theorem integral_eq_zero_of_translate (θ : AddChar F ℂ) (ν : Measure F) [ν.IsAddHaarMeasure] (Φ : F → ℂ) (t : F)
    (hΦ : ∀ y : F, Φ (y + t) = (θ t : ℂ) * Φ y) (ht : θ t ≠ 1) : ∫ y : F, Φ y ∂ν = 0 := by
  have h := integral_add_right_eq_self (μ := ν) Φ t
  simp_rw [hΦ] at h
  rw [integral_const_mul] at h
  have h2 : ((θ t : ℂ) - 1) * ∫ y : F, Φ y ∂ν = 0 := by rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) ht
  · exact h3

end Theta

section Jacquet

variable (p)

def jac (z₀ z₁ : ℂˣ) (θ : AddChar F ℂ) (ν : Measure F) (g : G) : ℂ :=
  ∫ y : F, sph p z₀ z₁ (antidiagonal2 p * unipotentGL2 y * g) * θ y ∂ν

theorem unipotent_eq (x : F) : (unipotent x : G) = unipotentGL2 x := by
  apply Units.ext
  rw [unipotentGL2_coe]
  rfl

theorem jac_unipotent_mul (z₀ z₁ : ℂˣ) (θ : AddChar F ℂ) (ν : Measure F) [ν.IsAddHaarMeasure] (x : F) (g : G) :
    jac p z₀ z₁ θ ν (unipotent x * g) = θ⁻¹ x * jac p z₀ z₁ θ ν g := by
  unfold jac
  have hfun : (fun y : F => sph p z₀ z₁ (antidiagonal2 p * unipotentGL2 y * (unipotent x * g)) * θ y) =
      fun y : F => θ (-x) * (sph p z₀ z₁ (antidiagonal2 p * unipotentGL2 (y + x) * g) * θ (y + x)) := by
    funext y
    rw [unipotent_eq, unipotentGL2_add, AddChar.map_add_eq_mul]
    have : θ (-x) * θ x = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    simp only [mul_assoc]
    linear_combination (sph p z₀ z₁ (antidiagonal2 p * (unipotentGL2 y * (unipotentGL2 x * g))) * θ y) * this.symm
  rw [hfun, integral_const_mul,
    integral_add_right_eq_self (μ := ν) (fun y : F => sph p z₀ z₁ (antidiagonal2 p * unipotentGL2 y * g) * θ y) x,
    AddChar.inv_apply]

theorem jac_mul_kzero (z₀ z₁ : ℂˣ) (θ : AddChar F ℂ) (ν : Measure F) {k : G} (hk : k ∈ kzero p) (g : G) :
    jac p z₀ z₁ θ ν (g * k) = jac p z₀ z₁ θ ν g := by
  unfold jac
  congr 1
  funext y
  rw [← mul_assoc, sph_mul _ _ hk]

variable (π : HeightOneSpectrum.adicCompletion ℚ p) (hπ : π ≠ 0) (hvπ : Valued.v π = WithZero.exp (-1 : ℤ))

theorem scalarPi_comm (h : G) : h * scalarPi π hπ = scalarPi π hπ * h := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, show ((scalarPi π hπ : G) : Mat) = !![π, 0; 0, π] from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem scalarPi_eq_diagonal2 : scalarPi π hπ = diagonal2 p ![Units.mk0 π hπ, Units.mk0 π hπ] := by
  apply Units.ext
  rw [show ((scalarPi π hπ : G) : Mat) = !![π, 0; 0, π] from rfl, diagonal2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp

include hvπ in

theorem sph_scalarPi_mul (z₀ z₁ : ℂˣ) (h : G) : sph p z₀ z₁ (scalarPi π hπ * h) = (z₀ : ℂ) * z₁ * sph p z₀ z₁ h := by
  rw [scalarPi_eq_diagonal2, sph_diagonal2_mul]
  have hhalf : halfModulus2 p ![Units.mk0 π hπ, Units.mk0 π hπ] = 1 := by
    unfold halfModulus2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mk0]
    rw [div_self (norm_ne_zero_iff.mpr hπ), Real.sqrt_one, Complex.ofReal_one]
  have hϖ' : Valued.v ((Units.mk0 π hπ : Fˣ) : F) = WithZero.exp (-1 : ℤ) := by rw [Units.val_mk0]; exact hvπ
  simp only [torusChar2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hhalf,
    unrChar_uniformizer p _ _ hϖ']
  ring

include hvπ in

theorem jac_mul_scalarPi (z₀ z₁ : ℂˣ) (θ : AddChar F ℂ) (ν : Measure F) (g : G) :
    jac p z₀ z₁ θ ν (g * scalarPi π hπ) = (z₀ : ℂ) * z₁ * jac p z₀ z₁ θ ν g := by
  unfold jac
  rw [← integral_const_mul]
  congr 1
  funext y
  have : antidiagonal2 p * unipotentGL2 y * (g * scalarPi π hπ) = scalarPi π hπ * (antidiagonal2 p * unipotentGL2 y * g) := by
    rw [← mul_assoc, scalarPi_comm]
  rw [this, sph_scalarPi_mul p π hπ hvπ]
  ring

end Jacquet

section Torus

variable (p)
variable (π : HeightOneSpectrum.adicCompletion ℚ p) (hπ : π ≠ 0) (hvπ : Valued.v π = WithZero.exp (-1 : ℤ))

def gm (z₀ z₁ : ℂˣ) (m : ℤ) (y : F) : ℂ := sph p z₀ z₁ (antidiagonal2 p * unipotentGL2 y * diagZ π hπ m)

include hvπ in
theorem v_pi_zpow' (k : ℤ) : Valued.v (π ^ (-k)) = WithZero.exp k := by
  rw [v_pi_zpow p π hvπ, neg_neg]

include hπ hvπ in
theorem measurableSet_ball_pi (k : ℤ) : MeasurableSet (ball p k) :=
  measurableSet_ball (zpow_ne_zero _ hπ) (v_pi_zpow' p π hvπ k)

include hπ hvπ in
theorem isCompact_ball_pi (k : ℤ) : IsCompact (ball p k) :=
  isCompact_ball (Units.mk0 (π ^ (-k)) (zpow_ne_zero _ hπ)) (by rw [Units.val_mk0]; exact v_pi_zpow' p π hvπ k)

include hvπ in

theorem far_zero (z₀ z₁ : ℂˣ) (θ : AddChar F ℂ) (hθ1 : ∃ x : F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ θ x ≠ 1)
    (ν : Measure F) [ν.IsAddHaarMeasure] (m : ℤ) :
    ∫ y : F in (ball p 1)ᶜ, gm p π hπ z₀ z₁ m y * θ y ∂ν = 0 := by
  obtain ⟨t, ht1, ht⟩ := hθ1
  rw [← integral_indicator (measurableSet_ball_pi p π hπ hvπ 1).compl]
  refine integral_eq_zero_of_translate θ ν _ t (fun y => ?_) ht
  by_cases hy : y ∈ ball p 1
  · have hy' : y + t ∈ ball p 1 := (add_mem_ball_iff ht1 y).mpr hy
    rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hy'), Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hy),
      mul_zero]
  · have hy' : y + t ∉ ball p 1 := fun h => hy ((add_mem_ball_iff ht1 y).mp h)
    rw [Set.indicator_of_mem (Set.mem_compl hy'), Set.indicator_of_mem (Set.mem_compl hy)]
    have hlt : Valued.v t < Valued.v y := lt_of_le_of_lt ht1 (not_le.mp hy)
    have hv : Valued.v (y + t) = Valued.v y := Valuation.map_add_eq_of_lt_left _ hlt
    rw [gm, gm, sph_weyl_congr p π hπ hvπ _ _ m hv, AddChar.map_add_eq_mul]
    ring

include hπ hvπ in

theorem ball_one_theta_zero (θ : AddChar F ℂ) (hθ1 : ∃ x : F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ θ x ≠ 1)
    (ν : Measure F) [ν.IsAddHaarMeasure] : ∫ y : F in ball p 1, θ y ∂ν = 0 := by
  obtain ⟨t, ht1, ht⟩ := hθ1
  rw [← integral_indicator (measurableSet_ball_pi p π hπ hvπ 1)]
  refine integral_eq_zero_of_translate θ ν _ t (fun y => ?_) ht
  by_cases hy : y ∈ ball p 1
  · rw [Set.indicator_of_mem ((add_mem_ball_iff ht1 y).mpr hy), Set.indicator_of_mem hy, AddChar.map_add_eq_mul]
    ring
  · rw [Set.indicator_of_notMem (fun h => hy ((add_mem_ball_iff ht1 y).mp h)), Set.indicator_of_notMem hy,
      mul_zero]

include hvπ in

theorem gm_succ (z₀ z₁ : ℂˣ) (m : ℤ) (y : F) :
    gm p π hπ z₀ z₁ (m + 1) y =
      ((z₀ : ℂ) * (((sR p : ℝ) : ℂ))⁻¹) * gm p π hπ z₀ z₁ m y +
        (((z₁ : ℂ) * ((sR p : ℝ) : ℂ) - (z₀ : ℂ) * (((sR p : ℝ) : ℂ))⁻¹) * (z₁ : ℂ) ^ m *
            ((sR p : ℝ) : ℂ) ^ m) * (ball p (-m - 1)).indicator (fun _ => (1 : ℂ)) y := by
  have hs := sC_ne_zero p
  have h0 : ((z₀ : ℂˣ) : ℂ) ≠ 0 := z₀.ne_zero
  have h1 : ((z₁ : ℂˣ) : ℂ) ≠ 0 := z₁.ne_zero
  by_cases hsm : Valued.v y ≤ WithZero.exp (-(m + 1))
  · rw [Set.indicator_of_mem (mem_ball.mpr (by rwa [show -m - 1 = -(m + 1) by ring])), gm,
      sph_weyl_small p π hπ hvπ _ _ (m + 1) hsm, gm,
      sph_weyl_small p π hπ hvπ _ _ m (hsm.trans (WithZero.exp_le_exp.mpr (by linarith))),
      zpow_add_one₀ h1, zpow_add_one₀ hs]
    ring
  · have hy0 : y ≠ 0 := by
      intro h; apply hsm; rw [h, map_zero]; exact zero_le'
    set j := lv p y with hjdef
    have hvy : Valued.v y = WithZero.exp j := (exp_lv p hy0).symm
    have hj : -(m + 1) < j := by
      rw [hvy, not_le, WithZero.exp_lt_exp] at hsm; exact hsm
    rw [Set.indicator_of_notMem (by rwa [mem_ball, show -m - 1 = -(m + 1) by ring]), mul_zero, add_zero, gm,
      sph_weyl_shell p π hπ hvπ _ _ (m + 1) j hj hvy, gm]
    rcases (show j = -m ∨ -m < j by omega) with hjm | hjm
    · rw [sph_weyl_small p π hπ hvπ _ _ m (by rw [hvy, hjm]), hjm, show -m + (m + 1) = 1 by ring, zpow_one,
        neg_neg, show -(m + 1) - 2 * -m = m - 1 by ring, zpow_sub_one₀ hs]
      ring
    · rw [sph_weyl_shell p π hπ hvπ _ _ m j hjm hvy, show j + (m + 1) = j + m + 1 by ring, zpow_add_one₀ h0,
        show -(m + 1) - 2 * j = -m - 2 * j - 1 by ring, zpow_sub_one₀ hs]
      ring

def Im (z₀ z₁ : ℂˣ) (θ : AddChar F ℂ) (ν : Measure F) (m : ℤ) : ℂ :=
  ∫ y : F in ball p 1, gm p π hπ z₀ z₁ m y * θ y ∂ν

include hπ hvπ in

theorem integrable_gm_general (z₀ z₁ : ℂˣ) (hz : ‖(z₀ : ℂ)‖ < ‖(z₁ : ℂ)‖) (θ : AddChar F ℂ)
    (hθ0 : ∀ x : F, Valued.v x ≤ 1 → θ x = 1) (ν : Measure F) [ν.IsAddHaarMeasure] (g : G) :
    Integrable (fun y : F => sph p z₀ z₁ (antidiagonal2 p * unipotentGL2 y * g) * θ y) ν := by
  have hϖ' : Valued.v ((Units.mk0 π hπ : Fˣ) : F) = WithZero.exp (-1 : ℤ) := by rw [Units.val_mk0]; exact hvπ
  have hcχ : ∀ i, ∀ u ∈ higherUnitsAt ℚ p ((fun _ => 0 : Fin 2 → ℕ) i),
      (![unrChar p z₀, unrChar p z₁] : Fin 2 → (Fˣ →* ℂˣ)) i u = 1 := by
    intro i u hu
    fin_cases i
    · exact unrChar_unram p z₀ u hu
    · exact unrChar_unram p z₁ u hu
  have hdom : ‖(((![unrChar p z₀, unrChar p z₁] : Fin 2 → (Fˣ →* ℂˣ)) 0 (Units.mk0 π hπ) : ℂˣ) : ℂ)‖ <
      ‖(((![unrChar p z₀, unrChar p z₁] : Fin 2 → (Fˣ →* ℂˣ)) 1 (Units.mk0 π hπ) : ℂˣ) : ℂ)‖ := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [unrChar_uniformizer p _ _ hϖ', unrChar_uniformizer p _ _ hϖ']
    exact hz
  exact integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2 p _ (fun _ => 0) hcχ
    (Units.mk0 π hπ) hϖ' hdom (sph p z₀ z₁) (sph_mem z₀ z₁) (antidiagonal2 p) (antidiagonal2_coe p) θ
    (continuous_theta θ hθ0) g ν

include hvπ in

theorem Im_succ (z₀ z₁ : ℂˣ) (hz : ‖(z₀ : ℂ)‖ < ‖(z₁ : ℂ)‖) (θ : AddChar F ℂ)
    (hθ0 : ∀ x : F, Valued.v x ≤ 1 → θ x = 1) (ν : Measure F) [ν.IsAddHaarMeasure] (m : ℤ) (hm : -1 ≤ m) :
    Im p π hπ z₀ z₁ θ ν (m + 1) =
      ((z₀ : ℂ) * (((sR p : ℝ) : ℂ))⁻¹) * Im p π hπ z₀ z₁ θ ν m +
        (((z₁ : ℂ) * ((sR p : ℝ) : ℂ) - (z₀ : ℂ) * (((sR p : ℝ) : ℂ))⁻¹) * (z₁ : ℂ) ^ m *
            ((sR p : ℝ) : ℂ) ^ m) *
          (((qR p ^ (-m - 1) * ν.real (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) : ℝ)) : ℂ) := by
  have hmeas1 := measurableSet_ball_pi p π hπ hvπ 1
  have hmeasB := measurableSet_ball_pi p π hπ hvπ (-m - 1)
  set c₁ : ℂ := (z₀ : ℂ) * (((sR p : ℝ) : ℂ))⁻¹
  set c₂ : ℂ := ((z₁ : ℂ) * ((sR p : ℝ) : ℂ) - (z₀ : ℂ) * (((sR p : ℝ) : ℂ))⁻¹) * (z₁ : ℂ) ^ m *
    ((sR p : ℝ) : ℂ) ^ m

  have hI1 : IntegrableOn (fun y : F => gm p π hπ z₀ z₁ m y * θ y) (ball p 1) ν :=
    (integrable_gm_general p π hπ hvπ z₀ z₁ hz θ hθ0 ν (diagZ π hπ m)).integrableOn
  have hθint : IntegrableOn (fun y : F => θ y) (ball p 1) ν :=
    (continuous_theta θ hθ0).continuousOn.integrableOn_compact (isCompact_ball_pi p π hπ hvπ 1)
  have hind_eq : (fun y : F => (ball p (-m - 1)).indicator (fun _ => (1 : ℂ)) y * θ y) =
      (ball p (-m - 1)).indicator (fun y : F => θ y) := by
    funext y
    by_cases hy : y ∈ ball p (-m - 1)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  have hI2 : IntegrableOn (fun y : F => (ball p (-m - 1)).indicator (fun _ => (1 : ℂ)) y * θ y) (ball p 1) ν := by
    rw [hind_eq]; exact hθint.indicator hmeasB

  have hstep : Im p π hπ z₀ z₁ θ ν (m + 1) =
      ∫ y : F in ball p 1, (c₁ * (gm p π hπ z₀ z₁ m y * θ y) +
        c₂ * ((ball p (-m - 1)).indicator (fun _ => (1 : ℂ)) y * θ y)) ∂ν := by
    unfold Im
    refine setIntegral_congr_fun hmeas1 fun y _ => ?_
    show _ = c₁ * (gm p π hπ z₀ z₁ m y * θ y) + c₂ * ((ball p (-m - 1)).indicator (fun _ => (1 : ℂ)) y * θ y)
    rw [gm_succ p π hπ hvπ z₀ z₁ m y]
    ring
  rw [hstep, integral_add (hI1.const_mul c₁) (hI2.const_mul c₂), integral_const_mul, integral_const_mul]
  unfold Im
  congr 1

  have hsub : ball p (-m - 1) ⊆ ball p 1 := fun y hy => hy.trans (WithZero.exp_le_exp.mpr (by linarith))
  have hsub0 : ball p (-m - 1) ⊆ ball p 0 := fun y hy => hy.trans (WithZero.exp_le_exp.mpr (by linarith))
  have hEq : Set.EqOn (fun y : F => θ y) (fun _ => (1 : ℂ)) (ball p (-m - 1)) :=
    fun y hy => theta_ball_zero θ hθ0 (hsub0 hy)
  rw [hind_eq, setIntegral_indicator hmeasB, Set.inter_eq_right.mpr hsub, setIntegral_congr_fun hmeasB hEq,
    setIntegral_const, measureReal_ball (Units.mk0 π hπ) (by rw [Units.val_mk0]; exact hvπ) ν (-m - 1)]
  simp only [Complex.real_smul, mul_one]

include hvπ in

theorem Im_neg_one (z₀ z₁ : ℂˣ) (θ : AddChar F ℂ) (hθ1 : ∃ x : F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ θ x ≠ 1)
    (ν : Measure F) [ν.IsAddHaarMeasure] : Im p π hπ z₀ z₁ θ ν (-1) = 0 := by
  unfold Im
  rw [setIntegral_congr_fun (measurableSet_ball_pi p π hπ hvπ 1) (fun y hy => by
      show gm p π hπ z₀ z₁ (-1) y * θ y = ((z₁ : ℂ) ^ (-1 : ℤ) * ((sR p : ℝ) : ℂ) ^ (-1 : ℤ)) * θ y
      rw [gm, sph_weyl_small p π hπ hvπ _ _ (-1) (by rw [neg_neg]; exact hy)]),
    integral_const_mul, ball_one_theta_zero p π hπ hvπ θ hθ1 ν, mul_zero]

include hvπ in

theorem Im_eq (z₀ z₁ : ℂˣ) (hz : ‖(z₀ : ℂ)‖ < ‖(z₁ : ℂ)‖) (θ : AddChar F ℂ)
    (hθ0 : ∀ x : F, Valued.v x ≤ 1 → θ x = 1) (hθ1 : ∃ x : F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ θ x ≠ 1)
    (ν : Measure F) [ν.IsAddHaarMeasure] (n : ℕ) :
    Im p π hπ z₀ z₁ θ ν ((n : ℤ) - 1) =
      ((ν.real (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) : ℝ) : ℂ) *
        (1 - (z₀ : ℂ) / ((z₁ : ℂ) * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ))) *
        (((sR p : ℝ) : ℂ) * ((z₁ : ℂ) ^ n - (z₀ : ℂ) ^ n) / (((z₁ : ℂ) - z₀) * (((sR p : ℝ) : ℂ)) ^ n)) := by
  have hs := sC_ne_zero p
  have h0 : ((z₀ : ℂˣ) : ℂ) ≠ 0 := z₀.ne_zero
  have h1 : ((z₁ : ℂˣ) : ℂ) ≠ 0 := z₁.ne_zero
  have hne : (z₁ : ℂ) - z₀ ≠ 0 := by
    intro h
    have : (z₁ : ℂ) = z₀ := sub_eq_zero.mp h
    rw [this] at hz
    exact lt_irrefl _ hz
  have hqR : ((qR p : ℝ) : ℂ) = ((sR p : ℝ) : ℂ) ^ 2 := by rw [← qC_eq, qC_eq_sC_sq]
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_sub, pow_zero, sub_self, mul_zero, zero_div]
      exact Im_neg_one p π hπ hvπ z₀ z₁ θ hθ1 ν
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℤ) - 1 = ((n : ℤ) - 1) + 1 by push_cast; ring,
        Im_succ p π hπ hvπ z₀ z₁ hz θ hθ0 ν _ (by linarith), ih, qC_eq_sC_sq]
      rw [zpow_sub_one₀ h1, zpow_sub_one₀ hs, zpow_natCast, zpow_natCast,
        show (-((n : ℤ) - 1) - 1) = -(n : ℤ) by ring, _root_.zpow_neg, zpow_natCast]
      push_cast
      rw [hqR]
      field_simp
      ring

theorem hecke_closed (z₀ z₁ : ℂ) (hne : z₁ - z₀ ≠ 0) (n : ℕ) :
    heckeRecursionSeq ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) (((sR p : ℝ) : ℂ) * (z₀ + z₁)) (z₀ * z₁) n =
      (z₁ ^ (n + 1) - z₀ ^ (n + 1)) / ((z₁ - z₀) * (((sR p : ℝ) : ℂ)) ^ n) := by
  have hs := sC_ne_zero p
  have key : ∀ n : ℕ,
      heckeRecursionSeq ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) (((sR p : ℝ) : ℂ) * (z₀ + z₁)) (z₀ * z₁) n =
        (z₁ ^ (n + 1) - z₀ ^ (n + 1)) / ((z₁ - z₀) * (((sR p : ℝ) : ℂ)) ^ n) ∧
      heckeRecursionSeq ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) (((sR p : ℝ) : ℂ) * (z₀ + z₁)) (z₀ * z₁) (n + 1) =
        (z₁ ^ (n + 2) - z₀ ^ (n + 2)) / ((z₁ - z₀) * (((sR p : ℝ) : ℂ)) ^ (n + 1)) := by
    intro n
    induction n with
    | zero =>
        constructor
        · rw [heckeRecursionSeq, eq_div_iff (mul_ne_zero hne (pow_ne_zero _ hs))]; ring
        · rw [heckeRecursionSeq, qC_eq_sC_sq, div_eq_div_iff (pow_ne_zero _ hs) (mul_ne_zero hne (pow_ne_zero _ hs))]
          ring
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        rw [heckeRecursionSeq, ih.1, ih.2, qC_eq_sC_sq,
          div_eq_div_iff (pow_ne_zero _ hs) (mul_ne_zero hne (pow_ne_zero _ hs))]
        field_simp
        ring
  exact (key n).1

end Torus

section Assembly

variable (p)
variable (π : HeightOneSpectrum.adicCompletion ℚ p) (hπ : π ≠ 0) (hvπ : Valued.v π = WithZero.exp (-1 : ℤ))

theorem diagZ_zero : diagZ π hπ 0 = (1 : G) := by
  apply Units.ext
  rw [show ((diagZ π hπ 0 : G) : Mat) = !![π ^ (0 : ℤ), 0; 0, 1] from rfl, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem diagZ_mul_unipotentGL2 (m : ℤ) (x : F) :
    diagZ π hπ m * unipotentGL2 x = unipotent (π ^ m * x) * diagZ π hπ m := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, unipotent_eq, unipotentGL2_coe, unipotentGL2_coe,
    show ((diagZ π hπ m : G) : Mat) = !![π ^ m, 0; 0, 1] from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem jac_one_eq_integral (z₀ z₁ : ℂˣ) (θ : AddChar F ℂ) (ν : Measure F) :
    ∫ y : F, sph p z₀ z₁ (antidiagonal2 p * unipotentGL2 y) * θ y ∂ν = jac p z₀ z₁ θ ν 1 := by
  unfold jac
  simp only [mul_one]

include hvπ in

theorem jac_diagZ_nat (z₀ z₁ : ℂˣ) (hz : ‖(z₀ : ℂ)‖ < ‖(z₁ : ℂ)‖) (θ : AddChar F ℂ)
    (hθ0 : ∀ x : F, Valued.v x ≤ 1 → θ x = 1) (hθ1 : ∃ x : F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ θ x ≠ 1)
    (ν : Measure F) [ν.IsAddHaarMeasure] (n : ℕ) :
    jac p z₀ z₁ θ ν (diagZ π hπ n) =
      ((ν.real (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) : ℝ) : ℂ) *
        (1 - (z₀ : ℂ) / ((z₁ : ℂ) * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ))) *
        (((z₁ : ℂ) ^ (n + 1) - (z₀ : ℂ) ^ (n + 1)) / (((z₁ : ℂ) - z₀) * (((sR p : ℝ) : ℂ)) ^ n)) := by
  have hs := sC_ne_zero p
  have hne : (z₁ : ℂ) - z₀ ≠ 0 := by
    intro h
    have : (z₁ : ℂ) = z₀ := sub_eq_zero.mp h
    rw [this] at hz
    exact lt_irrefl _ hz
  have hint := integrable_gm_general p π hπ hvπ z₀ z₁ hz θ hθ0 ν (diagZ π hπ n)
  have hsplit := integral_add_compl (measurableSet_ball_pi p π hπ hvπ 1) hint
  unfold jac
  rw [← hsplit]
  have hfar := far_zero p π hπ hvπ z₀ z₁ θ hθ1 ν n
  have hball := Im_eq p π hπ hvπ z₀ z₁ hz θ hθ0 hθ1 ν (n + 1)
  simp only [gm, Im] at hfar hball
  rw [show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring] at hball
  rw [hfar, add_zero, hball, pow_succ]
  field_simp
  ring

include hπ hvπ in

theorem jac_one (z₀ z₁ : ℂˣ) (hz : ‖(z₀ : ℂ)‖ < ‖(z₁ : ℂ)‖) (θ : AddChar F ℂ)
    (hθ0 : ∀ x : F, Valued.v x ≤ 1 → θ x = 1) (hθ1 : ∃ x : F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ θ x ≠ 1)
    (ν : Measure F) [ν.IsAddHaarMeasure] :
    jac p z₀ z₁ θ ν 1 =
      ((ν.real (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) : ℝ) : ℂ) *
        (1 - (z₀ : ℂ) / ((z₁ : ℂ) * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ))) := by
  have hne : (z₁ : ℂ) - z₀ ≠ 0 := by
    intro h
    have : (z₁ : ℂ) = z₀ := sub_eq_zero.mp h
    rw [this] at hz
    exact lt_irrefl _ hz
  have h := jac_diagZ_nat p π hπ hvπ z₀ z₁ hz θ hθ0 hθ1 ν 0
  rw [Nat.cast_zero, diagZ_zero] at h
  rw [h]
  simp only [zero_add, pow_one, pow_zero, mul_one, div_self hne]

include hvπ in

theorem jac_diagZ_neg (z₀ z₁ : ℂˣ) (θ : AddChar F ℂ) (hθ1 : ∃ x : F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ θ x ≠ 1)
    (ν : Measure F) [ν.IsAddHaarMeasure] (m : ℤ) (hm : m < 0) : jac p z₀ z₁ θ ν (diagZ π hπ m) = 0 := by
  obtain ⟨t, ht1, ht⟩ := hθ1
  set x : F := π ^ (-m) * t with hx
  have hxv : Valued.v x ≤ 1 := by
    rw [hx, map_mul, v_pi_zpow' p π hvπ]
    calc WithZero.exp m * Valued.v t ≤ WithZero.exp m * WithZero.exp 1 := mul_le_mul_right ht1 _
      _ = WithZero.exp (m + 1) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp 0 := WithZero.exp_le_exp.mpr (by omega)
      _ = 1 := WithZero.exp_zero
  have hk : (unipotentGL2 x : G) ∈ kzero p := unipotentGL2_mem_kzero hxv
  have hpx : π ^ m * x = t := by
    rw [hx, ← mul_assoc, ← zpow_add₀ hπ, add_neg_cancel, zpow_zero, one_mul]
  have h1 := jac_mul_kzero p z₀ z₁ θ ν hk (diagZ π hπ m)
  rw [diagZ_mul_unipotentGL2, hpx, jac_unipotent_mul] at h1

  have hne : θ⁻¹ t ≠ 1 := by
    intro h
    apply ht
    have hmul : θ⁻¹ t * θ t = 1 := by
      rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    rwa [h, one_mul] at hmul
  have h2 : (θ⁻¹ t - 1) * jac p z₀ z₁ θ ν (diagZ π hπ m) = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hne
  · exact h3

include hvπ in

theorem jac_diagZ (z₀ z₁ : ℂˣ) (hz : ‖(z₀ : ℂ)‖ < ‖(z₁ : ℂ)‖) (θ : AddChar F ℂ)
    (hθ0 : ∀ x : F, Valued.v x ≤ 1 → θ x = 1) (hθ1 : ∃ x : F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ θ x ≠ 1)
    (ν : Measure F) [ν.IsAddHaarMeasure] (m : ℤ) :
    jac p z₀ z₁ θ ν (diagZ π hπ m) =
      jac p z₀ z₁ θ ν 1 *
        torusFactor ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) (((sR p : ℝ) : ℂ) * ((z₀ : ℂ) + z₁)) ((z₀ : ℂ) * z₁) m := by
  have hne : (z₁ : ℂ) - z₀ ≠ 0 := by
    intro h
    have : (z₁ : ℂ) = z₀ := sub_eq_zero.mp h
    rw [this] at hz
    exact lt_irrefl _ hz
  rcases lt_or_ge m 0 with hm | hm
  · rw [jac_diagZ_neg p π hπ hvπ z₀ z₁ θ hθ1 ν m hm, torusFactor, if_neg (not_le.mpr hm), mul_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [torusFactor, if_pos hm, Int.toNat_natCast, hecke_closed p _ _ hne n,
      jac_diagZ_nat p π hπ hvπ z₀ z₁ hz θ hθ0 hθ1 ν n, jac_one p π hπ hvπ z₀ z₁ hz θ hθ0 hθ1 ν]

end Assembly

section Iwasawa

variable (p)

theorem antidiagonal2_mul_self : antidiagonal2 p * antidiagonal2 p = (1 : G) := by
  apply Units.ext
  rw [Units.val_mul, antidiagonal2_coe, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem antidiagonal2_inv : (antidiagonal2 p)⁻¹ = antidiagonal2 p :=
  inv_eq_of_mul_eq_one_right (antidiagonal2_mul_self p)

theorem antidiagonal2_mem_kzero : antidiagonal2 p ∈ kzero p := by
  refine mem_kzero_of_integral (fun i j => ?_) (fun i j => ?_)
  · rw [antidiagonal2_coe]; fin_cases i <;> fin_cases j <;> simp
  · rw [antidiagonal2_inv, antidiagonal2_coe]; fin_cases i <;> fin_cases j <;> simp

def lowerUnip (t : F) : G := antidiagonal2 p * unipotentGL2 t * antidiagonal2 p

theorem lowerUnip_coe (t : F) : ((lowerUnip p t : G) : Mat) = !![1, 0; t, 1] := by
  rw [lowerUnip, Units.val_mul, Units.val_mul, antidiagonal2_coe, unipotentGL2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lowerUnip_mem_kzero {t : F} (ht : Valued.v t ≤ 1) : lowerUnip p t ∈ kzero p :=
  mul_mem (mul_mem (antidiagonal2_mem_kzero p) (unipotentGL2_mem_kzero ht)) (antidiagonal2_mem_kzero p)

theorem iwasawa_of_le (g : G) (h : Valued.v ((g : Mat) 1 0) ≤ Valued.v ((g : Mat) 1 1)) :
    ∃ k ∈ kzero p, ∃ (a : Fin 2 → Fˣ) (x : F), g * k = diagonal2 p a * upperUnipotent2 p x := by
  have hdet : (g : Mat) 0 0 * (g : Mat) 1 1 - (g : Mat) 0 1 * (g : Mat) 1 0 ≠ 0 := by
    have := det_ne_zero p g
    rwa [Matrix.det_fin_two] at this
  have hD : (g : Mat) 1 1 ≠ 0 := by
    intro hD
    have hC : (g : Mat) 1 0 = 0 := by
      have h' : Valued.v ((g : Mat) 1 0) ≤ 0 := by rw [hD, map_zero] at h; exact h
      exact (Valuation.zero_iff _).mp (le_antisymm h' zero_le')
    apply hdet
    rw [hD, hC]; ring
  have hE : (g : Mat) 0 0 - (g : Mat) 0 1 * (g : Mat) 1 0 / (g : Mat) 1 1 ≠ 0 := by
    intro h0
    apply hdet
    have : ((g : Mat) 0 0 - (g : Mat) 0 1 * (g : Mat) 1 0 / (g : Mat) 1 1) * (g : Mat) 1 1 =
        (g : Mat) 0 0 * (g : Mat) 1 1 - (g : Mat) 0 1 * (g : Mat) 1 0 := by
      field_simp
    rw [← this, h0, zero_mul]
  have hval : Valued.v (-(g : Mat) 1 0 / (g : Mat) 1 1) ≤ 1 := by
    rw [map_div₀, Valuation.map_neg]
    exact div_le_one_of_le₀ h zero_le'
  refine ⟨lowerUnip p (-(g : Mat) 1 0 / (g : Mat) 1 1), lowerUnip_mem_kzero p hval,
    ![Units.mk0 _ hE, Units.mk0 _ hD],
    (g : Mat) 0 1 / ((g : Mat) 0 0 - (g : Mat) 0 1 * (g : Mat) 1 0 / (g : Mat) 1 1), ?_⟩
  apply Units.ext
  rw [Units.val_mul, lowerUnip_coe, Units.val_mul, diagonal2_coe, upperUnipotent2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;> (try field_simp) <;> ring

theorem iwasawa (g : G) :
    ∃ k ∈ kzero p, ∃ (a : Fin 2 → Fˣ) (x : F), g * k = diagonal2 p a * upperUnipotent2 p x := by
  rcases le_total (Valued.v ((g : Mat) 1 0)) (Valued.v ((g : Mat) 1 1)) with h | h
  · exact iwasawa_of_le p g h
  · have h' : Valued.v (((g * antidiagonal2 p : G) : Mat) 1 0) ≤ Valued.v (((g * antidiagonal2 p : G) : Mat) 1 1) := by
      rw [Units.val_mul, antidiagonal2_coe]
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
    obtain ⟨k, hk, a, x, hgk⟩ := iwasawa_of_le p (g * antidiagonal2 p) h'
    exact ⟨antidiagonal2 p * k, mul_mem (antidiagonal2_mem_kzero p) hk, a, x, by rw [← mul_assoc]; exact hgk⟩

theorem ps_apply_eq (χ : Fin 2 → (Fˣ →* ℂˣ)) {f : G → ℂ} (hf : f ∈ principalSeries2 p χ)
    (hfK : ∀ k g : G, k ∈ kzero p → f (g * k) = f g) {g k : G} (hk : k ∈ kzero p) {a : Fin 2 → Fˣ} {x : F}
    (hgk : g * k = diagonal2 p a * upperUnipotent2 p x) :
    f g = torusChar2 p χ a * halfModulus2 p a * f 1 := by
  obtain ⟨-, hn, ht⟩ := mem_principalSeries2_iff.mp hf
  have h1 : f (upperUnipotent2 p x) = f 1 := by
    have := hn x 1
    rwa [mul_one] at this
  rw [← hfK k g hk, hgk, ht, h1]

theorem ps_unique (χ : Fin 2 → (Fˣ →* ℂˣ)) {f f' : G → ℂ} (hf : f ∈ principalSeries2 p χ)
    (hf' : f' ∈ principalSeries2 p χ) (hfK : ∀ k g : G, k ∈ kzero p → f (g * k) = f g)
    (hf'K : ∀ k g : G, k ∈ kzero p → f' (g * k) = f' g) (h1 : f 1 = f' 1) : f = f' := by
  funext g
  obtain ⟨k, hk, a, x, hgk⟩ := iwasawa p g
  rw [ps_apply_eq p χ hf hfK hk hgk, ps_apply_eq p χ hf' hf'K hk hgk, h1]

theorem unram_eq_unrChar (χ : Fˣ →* ℂˣ) (hχ : ∀ u ∈ higherUnitsAt ℚ p 0, χ u = 1) (ϖ : Fˣ)
    (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) : χ = unrChar p (χ ϖ) := by
  refine MonoidHom.ext fun a => ?_
  have hu : a * ϖ ^ (lv p (a : F)) ∈ higherUnitsAt ℚ p 0 := by
    rw [mem_higherUnitsAt_zero_iff, Units.val_mul, map_mul, valued_units_zpow ϖ hϖ, ← exp_lv p a.ne_zero,
      ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  have h := hχ _ hu
  rw [map_mul, map_zpow, mul_eq_one_iff_eq_inv, ← _root_.zpow_neg] at h
  rw [h]
  rfl

theorem chi_eq (χ : Fin 2 → (Fˣ →* ℂˣ)) (hχ : ∀ i, ∀ u ∈ higherUnitsAt ℚ p 0, χ i u = 1) (ϖ : Fˣ)
    (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) :
    χ = ![unrChar p (χ 0 ϖ), unrChar p (χ 1 ϖ)] := by
  funext i
  fin_cases i
  · exact unram_eq_unrChar p (χ 0) (hχ 0) ϖ hϖ
  · exact unram_eq_unrChar p (χ 1) (hχ 1) ϖ hϖ

theorem eq_sph (χ : Fin 2 → (Fˣ →* ℂˣ)) (hχ : ∀ i, ∀ u ∈ higherUnitsAt ℚ p 0, χ i u = 1) (ϖ : Fˣ)
    (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) {f : G → ℂ} (hf : f ∈ principalSeries2 p χ)
    (hfK : ∀ k g : G, k ∈ kzero p → f (g * k) = f g) (hf1 : f 1 = 1) :
    f = sph p (χ 0 ϖ) (χ 1 ϖ) := by
  have hχ' := chi_eq p χ hχ ϖ hϖ
  rw [hχ'] at hf
  exact ps_unique p _ hf (sph_mem _ _) hfK (fun k g hk => sph_mul _ _ hk g) (by rw [hf1, sph_one])

end Iwasawa

section Main

variable (p)
variable (π : HeightOneSpectrum.adicCompletion ℚ p) (hπ : π ≠ 0) (hvπ : Valued.v π = WithZero.exp (-1 : ℤ))

theorem qC_cpow_half : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (1 / 2 : ℂ) = ((sR p : ℝ) : ℂ) := by
  rw [qC_eq, show ((1 / 2 : ℂ)) = (((1 / 2 : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (qR_pos p).le]
  congr 1
  rw [sR, Real.sqrt_eq_rpow]

include hvπ in

theorem main (θ : AddChar F ℂ) (hθ0 : ∀ x : F, Valued.v x ≤ 1 → θ x = 1)
    (hθ1 : ∃ x : F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ θ x ≠ 1)
    (χ : Fin 2 → (Fˣ →* ℂˣ)) (hχ : ∀ i, ∀ u ∈ higherUnitsAt ℚ p 0, χ i u = 1)
    (hdom : ‖((χ 0 (Units.mk0 π hπ) : ℂˣ) : ℂ)‖ < ‖((χ 1 (Units.mk0 π hπ) : ℂˣ) : ℂ)‖)
    (f : G → ℂ) (hf : f ∈ principalSeries2 p χ) (hfK : ∀ k g : G, k ∈ kzero p → f (g * k) = f g)
    (hf1 : f 1 = 1) (ν : Measure F) [ν.IsAddHaarMeasure] :
    (∀ g : G, Integrable (fun y : F => f (antidiagonal2 p * unipotentGL2 y * g) * θ y) ν) ∧
    (∫ y, f (antidiagonal2 p * unipotentGL2 y) * θ y ∂ν =
      ((ν.real (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) : ℝ) : ℂ) *
        (1 - ((χ 0 (Units.mk0 π hπ) : ℂˣ) : ℂ) /
          (((χ 1 (Units.mk0 π hπ) : ℂˣ) : ℂ) * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ)))) ∧
    (∫ y, f (antidiagonal2 p * unipotentGL2 y) * θ y ∂ν ≠ 0) ∧
    (∀ (x : F) (g : G), ∫ y, f (antidiagonal2 p * unipotentGL2 y * (unipotent x * g)) * θ y ∂ν =
      θ⁻¹ x * ∫ y, f (antidiagonal2 p * unipotentGL2 y * g) * θ y ∂ν) ∧
    (∀ k g : G, k ∈ kzero p →
      ∫ y, f (antidiagonal2 p * unipotentGL2 y * (g * k)) * θ y ∂ν =
        ∫ y, f (antidiagonal2 p * unipotentGL2 y * g) * θ y ∂ν) ∧
    (∀ g : G, ∫ y, f (antidiagonal2 p * unipotentGL2 y * (g * scalarPi π hπ)) * θ y ∂ν =
      ((χ 0 (Units.mk0 π hπ) : ℂˣ) : ℂ) * ((χ 1 (Units.mk0 π hπ) : ℂˣ) : ℂ) *
        ∫ y, f (antidiagonal2 p * unipotentGL2 y * g) * θ y ∂ν) ∧
    (∀ m : ℤ, ∫ y, f (antidiagonal2 p * unipotentGL2 y * diagZ π hπ m) * θ y ∂ν =
      (∫ y, f (antidiagonal2 p * unipotentGL2 y) * θ y ∂ν) *
        torusFactor ((Ideal.absNorm p.asIdeal : ℕ) : ℂ)
          (((sR p : ℝ) : ℂ) * (((χ 0 (Units.mk0 π hπ) : ℂˣ) : ℂ) + ((χ 1 (Units.mk0 π hπ) : ℂˣ) : ℂ)))
          (((χ 0 (Units.mk0 π hπ) : ℂˣ) : ℂ) * ((χ 1 (Units.mk0 π hπ) : ℂˣ) : ℂ)) m) := by
  have hϖu : Valued.v ((Units.mk0 π hπ : Fˣ) : F) = WithZero.exp (-1 : ℤ) := by rw [Units.val_mk0]; exact hvπ
  have hfs := eq_sph p χ hχ (Units.mk0 π hπ) hϖu hf hfK hf1
  subst hfs
  set z₀ : ℂˣ := χ 0 (Units.mk0 π hπ)
  set z₁ : ℂˣ := χ 1 (Units.mk0 π hπ)
  refine ⟨fun g => integrable_gm_general p π hπ hvπ z₀ z₁ hdom θ hθ0 ν g, ?_, ?_,
    fun x g => jac_unipotent_mul p z₀ z₁ θ ν x g, fun k g hk => jac_mul_kzero p z₀ z₁ θ ν hk g,
    fun g => jac_mul_scalarPi p π hπ hvπ z₀ z₁ θ ν g, fun m => ?_⟩
  · rw [jac_one_eq_integral, jac_one p π hπ hvπ z₀ z₁ hdom θ hθ0 hθ1 ν]
  · rw [jac_one_eq_integral, jac_one p π hπ hvπ z₀ z₁ hdom θ hθ0 hθ1 ν]
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast (measureReal_integers_pos ν).ne'
    · intro h
      have h1 : (z₀ : ℂ) = (z₁ : ℂ) * ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) := by
        have h' := (sub_eq_zero.mp h).symm
        rw [div_eq_iff (mul_ne_zero z₁.ne_zero (qC_ne_zero p)), one_mul] at h'
        exact h'
      have hq : (1 : ℝ) ≤ ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by
        exact_mod_cast (HeightOneSpectrum.one_lt_absNorm p).le
      have : ‖(z₁ : ℂ)‖ ≤ ‖(z₀ : ℂ)‖ := by
        rw [h1, norm_mul, Complex.norm_natCast]
        exact le_mul_of_one_le_right (norm_nonneg _) hq
      exact (not_lt.mpr this) hdom
  · rw [jac_one_eq_integral]
    exact jac_diagZ p π hπ hvπ z₀ z₁ hdom θ hθ0 hθ1 ν m

end Main

section Psi

variable (p)

theorem psi_triv (x : F) (hx : Valued.v x ≤ 1) : NumberField.StandardAddChar.psiLocal ℚ p x = 1 :=
  psiLocal_eq_one_of_mem_integers ℚ p x ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mpr hx)

theorem psiInv_triv (x : F) (hx : Valued.v x ≤ 1) : (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x = 1 := by
  rw [AddChar.inv_apply]
  exact psi_triv p (-x) (by rwa [Valuation.map_neg])

theorem psi_nontriv :
    ∃ x : F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ NumberField.StandardAddChar.psiLocal ℚ p x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  set S : Set ℤ := {n : ℤ | ∀ x : F, Valued.v x ≤ WithZero.exp n → NumberField.StandardAddChar.psiLocal ℚ p x = 1}
    with hS
  have hlevel : sSup S = 0 := addCharLevel_psiLocal_rat p
  have hne : ∃ x₀ : F, NumberField.StandardAddChar.psiLocal ℚ p x₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact psiLocal_ne_one ℚ p (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀0 : x₀ ≠ 0 := by
    intro h; rw [h, AddChar.map_zero_eq_one] at hx₀; exact hx₀ rfl
  have hbdd : BddAbove S := by
    refine ⟨WithZero.log (Valued.v x₀), fun n hn => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hvx : Valued.v x₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx₀0
    have : Valued.v x₀ ≤ WithZero.exp n := by
      rw [← WithZero.exp_log hvx, WithZero.exp_le_exp]
      exact hlt.le
    exact hx₀ (hn x₀ this)
  have h1 : (1 : ℤ) ∈ S := hcon
  have := le_csSup hbdd h1
  rw [hlevel] at this
  exact absurd this (by norm_num)

theorem psiInv_nontriv :
    ∃ x : F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x ≠ 1 := by
  obtain ⟨x, hx, hne⟩ := psi_nontriv p
  refine ⟨-x, by rwa [Valuation.map_neg], ?_⟩
  rwa [AddChar.inv_apply, neg_neg]

end Psi

end KcSphJacquetRekey

open KcSphJacquetRekey in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → χ i u = 1)
    (hdom : ‖((χ 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)‖ <
      ‖((χ 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)‖)
    (f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 v χ)
    (hfK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → f (g * k) = f g)
    (hf1 : f 1 = 1)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localBorel ℚ v
    ∀ (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      (∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        Integrable (fun y : v.adicCompletion ℚ =>
          f (w₀ * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ y) ν) ∧
      let J : GL (Fin 2) (v.adicCompletion ℚ) → ℂ := fun g =>
        ∫ y, f (w₀ * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ y ∂ν
      let α₀ : ℂ := ((χ 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)
      let α₁ : ℂ := ((χ 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)
      (∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
          J (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * J g) ∧
      (∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → J (g * k) = J g) ∧
      (∀ g : GL (Fin 2) (v.adicCompletion ℚ),
          J (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = α₀ * α₁ * J g) ∧
      J 1 = ((ν {y : v.adicCompletion ℚ | Valued.v y ≤ 1}).toReal : ℂ) *
              (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * α₀ / α₁) ∧
      J 1 ≠ 0 ∧
      (∀ m : ℤ, J (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
          J 1 * torusFactor (Ideal.absNorm v.asIdeal : ℂ)
            ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (α₀ + α₁)) (α₀ * α₁) m) := by
  intro ν _

  have hw : w₀ = antidiagonal2 v := Units.ext (hw₀.trans (antidiagonal2_coe v).symm)
  subst hw

  have hχ' : ∀ i, ∀ u ∈ higherUnitsAt ℚ v 0, χ i u = 1 := fun i u hu =>
    hχ i u ((mem_higherUnitsAt_zero_iff ℚ v).mp hu)
  obtain ⟨hI, hJ1, hJ1ne, hlaw, hK, hcen, htor⟩ :=
    main v _ hπ hϖ (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (psiInv_triv v) (psiInv_nontriv v)
      χ hχ' hdom f hf hfK hf1 ν
  have hint : (HeightOneSpectrum.adicCompletionIntegers ℚ v : Set (v.adicCompletion ℚ)) =
      {x : v.adicCompletion ℚ | Valued.v x ≤ 1} := by
    ext x; simp [HeightOneSpectrum.mem_adicCompletionIntegers]
  refine ⟨hI, ?_⟩
  dsimp only
  simp only [mul_one]
  refine ⟨fun x g => ?_, hK, hcen, ?_, hJ1ne, fun m => ?_⟩
  · rw [hlaw x g, inv_inv]
  · rw [hJ1, Measure.real, hint]
    congr 1
    have hz₁ : ((χ 1 (Units.mk0 _ hπ) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hq := qC_ne_zero v
    field_simp
  · rw [htor m, show ((1 : ℂ) / 2) = (1 / 2 : ℂ) from rfl, qC_cpow_half]

end

end S_LanglandsTunnell_CubicInduction_jacquetIntegral_spherical_laws_of_unramified_of_norm_lt
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetIntegral_spherical_laws_of_unramified_of_norm_lt (solution)
