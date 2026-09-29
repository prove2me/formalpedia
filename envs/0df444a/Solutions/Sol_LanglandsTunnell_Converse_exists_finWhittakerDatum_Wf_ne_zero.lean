-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_finWhittakerDatum_Wf_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/4400a7e9-e86f-575c-aaea-20d2e70e46ec

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_sub_algebraMap_mem_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_finWhittakerDatum_Wf_ne_zero
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one"
p2m_attr_erase "simp" "AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

section

open Matrix
open scoped WithZero

namespace LocalWhittaker

variable {F : Type*} [Field F]

private def _root_.LocalWhittaker.unipotent (x : F) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [det_fin_two_of])

p2m_export "LocalWhittaker" "unipotent"

private def diagZ (π : F) (hπ : π ≠ 0) (m : ℤ) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![π ^ m, 0; 0, 1] (by simp [det_fin_two_of, zpow_ne_zero m hπ])

private def scalarPi (π : F) (hπ : π ≠ 0) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![π, 0; 0, π] (by simp [det_fin_two_of, hπ])

private theorem coe_unipotent
    (x : F) : ((unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl

private theorem coe_diagZ (π : F) (hπ : π ≠ 0) (m : ℤ) :
    ((diagZ π hπ m : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![π ^ m, 0; 0, 1] := rfl

private theorem coe_scalarPi (π : F) (hπ : π ≠ 0) :
    ((scalarPi π hπ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![π, 0; 0, π] := rfl

private theorem scalarPi_eq (π : F) (hπ : π ≠ 0) :
    scalarPi π hπ = Units.map (Matrix.scalar (Fin 2)).toMonoidHom (Units.mk0 π hπ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarPi, Matrix.scalar_apply, Matrix.diagonal]

private theorem coe_scalarPi_zpow (π : F) (hπ : π ≠ 0) (n : ℤ) :
    ((scalarPi π hπ ^ n : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) (π ^ n) := by
  rw [scalarPi_eq, ← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rfl

private theorem scalar_fin_two (c : F) : Matrix.scalar (Fin 2) c = !![c, 0; 0, c] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

private def integerUnit (v : Valuation F ℤᵐ⁰) (u : F) (hu : v u = 1) : (v.integer)ˣ where
  val := ⟨u, by simp [Valuation.mem_integer_iff, hu]⟩
  inv := ⟨u⁻¹, by simp [Valuation.mem_integer_iff, map_inv₀, hu]⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ (by rintro rfl; simp at hu))
  inv_val := Subtype.ext (inv_mul_cancel₀ (by rintro rfl; simp at hu))

private theorem exists_zpow_mul_of_ne_zero
    (v : Valuation F ℤᵐ⁰) {π : F} (hπ0 : π ≠ 0) (hπ : v π = WithZero.exp (-1 : ℤ))
    {e : F} (he : e ≠ 0) : ∃ (n : ℤ) (u : F), v u = 1 ∧ e = π ^ n * u := by
  have hve : v e ≠ 0 := (Valuation.ne_zero_iff v).mpr he
  refine ⟨-WithZero.log (v e), e / π ^ (-WithZero.log (v e)), ?_, ?_⟩
  · rw [map_div₀, map_zpow₀, hπ, ← WithZero.exp_zsmul, div_eq_one_iff_eq (WithZero.exp_ne_zero)]
    rw [← WithZero.exp_log hve]
    congr 1
    simp
  · rw [mul_div_cancel₀ _ (zpow_ne_zero _ hπ0)]

private theorem exists_iwasawa (v : Valuation F ℤᵐ⁰) (π : F) (hπ0 : π ≠ 0) (hπ : v π = WithZero.exp (-1 : ℤ))
    (g : GL (Fin 2) F) :
    ∃ (x : F) (m n : ℤ) (k : GL (Fin 2) v.integer),
      g = unipotent x * diagZ π hπ0 m * scalarPi π hπ0 ^ n * GeneralLinearGroup.map v.integer.subtype k := by

  have hdet : ((g : Matrix (Fin 2) (Fin 2) F)).det ≠ 0 := (Matrix.GeneralLinearGroup.det_ne_zero g)
  obtain ⟨k₀, a', b', e, ha', he, hgk⟩ : ∃ (k₀ : GL (Fin 2) v.integer) (a' b' e : F), a' ≠ 0 ∧ e ≠ 0 ∧
      ((g * GeneralLinearGroup.map v.integer.subtype k₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = !![a', b'; 0, e] := by
    set A := (g : Matrix (Fin 2) (Fin 2) F) with hA
    have hdet2 : A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0 := by rwa [Matrix.det_fin_two] at hdet
    by_cases hcd : v (A 1 1) ≤ v (A 1 0)
    ·
      have hc : A 1 0 ≠ 0 := by
        intro h0
        rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at hcd
        exact hdet2 (by rw [h0, hcd]; ring)
      set t : F := A 1 1 / A 1 0 with ht
      have htI : t ∈ v.integer := by
        rw [Valuation.mem_integer_iff, ht, map_div₀, div_le_one₀ (by simpa using (Valuation.pos_iff v).mpr hc)]
        exact hcd
      obtain ⟨k₀, hk₀⟩ : ∃ k₀ : GL (Fin 2) v.integer,
          (k₀ : Matrix (Fin 2) (Fin 2) v.integer) = !![-⟨t, htI⟩, 1; 1, 0] :=
        ⟨⟨!![-⟨t, htI⟩, 1; 1, 0], !![0, 1; 1, ⟨t, htI⟩],
          by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
          by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩, rfl⟩
      refine ⟨k₀, -(A 0 0 * A 1 1 - A 0 1 * A 1 0) / A 1 0, A 0 0, A 1 0, by
        exact div_ne_zero (neg_ne_zero.mpr hdet2) hc, hc, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [GeneralLinearGroup.map, Units.coe_map, RingHom.mapMatrix_apply, hk₀, Units.val_mul, Matrix.mul_apply,
          Fin.sum_univ_two, ht] <;>
        (try field_simp) <;> (try ring)
    ·
      rw [not_le] at hcd
      have hd : A 1 1 ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hcd
        exact absurd hcd (not_lt.mpr zero_le')
      set s : F := A 1 0 / A 1 1 with hs
      have hsI : s ∈ v.integer := by
        rw [Valuation.mem_integer_iff, hs, map_div₀, div_le_one₀ (by simpa using (Valuation.pos_iff v).mpr hd)]
        exact hcd.le
      obtain ⟨k₀, hk₀⟩ : ∃ k₀ : GL (Fin 2) v.integer,
          (k₀ : Matrix (Fin 2) (Fin 2) v.integer) = !![1, 0; -⟨s, hsI⟩, 1] :=
        ⟨⟨!![1, 0; -⟨s, hsI⟩, 1], !![1, 0; ⟨s, hsI⟩, 1],
          by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
          by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩, rfl⟩
      refine ⟨k₀, (A 0 0 * A 1 1 - A 0 1 * A 1 0) / A 1 1, A 0 1, A 1 1, div_ne_zero hdet2 hd, hd, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [GeneralLinearGroup.map, Units.coe_map, RingHom.mapMatrix_apply, hk₀, Units.val_mul, Matrix.mul_apply,
          Fin.sum_univ_two, hs] <;>
        (try field_simp) <;> (try ring)

  obtain ⟨n, u₂, hu₂, rfl⟩ := exists_zpow_mul_of_ne_zero v hπ0 hπ he
  obtain ⟨j, u₁, hu₁, rfl⟩ := exists_zpow_mul_of_ne_zero v hπ0 hπ ha'
  have hu₁0 : u₁ ≠ 0 := by rintro rfl; simp at hu₁
  have hu₂0 : u₂ ≠ 0 := by rintro rfl; simp at hu₂

  obtain ⟨D, hDval⟩ : ∃ D : GL (Fin 2) v.integer, (D : Matrix (Fin 2) (Fin 2) v.integer)
      = !![((integerUnit v u₁ hu₁ : (v.integer)ˣ) : v.integer), 0;
           0, ((integerUnit v u₂ hu₂ : (v.integer)ˣ) : v.integer)] :=
    ⟨⟨!![((integerUnit v u₁ hu₁ : (v.integer)ˣ) : v.integer), 0;
         0, ((integerUnit v u₂ hu₂ : (v.integer)ˣ) : v.integer)],
      !![(((integerUnit v u₁ hu₁)⁻¹ : (v.integer)ˣ) : v.integer), 0;
         0, (((integerUnit v u₂ hu₂)⁻¹ : (v.integer)ˣ) : v.integer)],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩, rfl⟩
  refine ⟨b' / (π ^ n * u₂), j - n, n, D * k₀⁻¹, ?_⟩
  rw [map_mul, map_inv, ← mul_assoc, eq_mul_inv_iff_mul_eq]
  have hD : ((GeneralLinearGroup.map v.integer.subtype D : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = !![u₁, 0; 0, u₂] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [GeneralLinearGroup.map, Units.coe_map, RingHom.mapMatrix_apply, hDval, Matrix.map_apply, integerUnit]
  have hπn : π ^ n ≠ 0 := zpow_ne_zero n hπ0
  ext i j'
  rw [hgk]
  simp only [Units.val_mul, coe_unipotent, coe_diagZ, coe_scalarPi_zpow, scalar_fin_two, hD]
  fin_cases i <;> fin_cases j' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, zpow_sub₀ hπ0, hu₁0] <;>
    (try field_simp)

section Invariants

variable (v : Valuation F ℤᵐ⁰)

private def bottomVal (g : GL (Fin 2) F) : ℤᵐ⁰ :=
  max (v ((g : Matrix (Fin 2) (Fin 2) F) 1 0)) (v ((g : Matrix (Fin 2) (Fin 2) F) 1 1))

private noncomputable def chosenCol (g : GL (Fin 2) F) : Fin 2 :=
  if v ((g : Matrix (Fin 2) (Fin 2) F) 1 1) ≤ v ((g : Matrix (Fin 2) (Fin 2) F) 1 0) then 0 else 1

private def bottomOrd (g : GL (Fin 2) F) : ℤ := -WithZero.log (bottomVal v g)

private def detOrd (g : GL (Fin 2) F) : ℤ := -WithZero.log (v ((g : Matrix (Fin 2) (Fin 2) F).det))

private def torusIndex (g : GL (Fin 2) F) : ℤ := detOrd v g - 2 * bottomOrd v g

private noncomputable def unipCoord (g : GL (Fin 2) F) : F :=
  (g : Matrix (Fin 2) (Fin 2) F) 0 (chosenCol v g) / (g : Matrix (Fin 2) (Fin 2) F) 1 (chosenCol v g)

private noncomputable def localW (ψ : F → ℂ) (c : ℤ → ℂ) (om : ℂ) (g : GL (Fin 2) F) : ℂ :=
  ψ (unipCoord v g) * c (torusIndex v g) * om ^ bottomOrd v g

private theorem val_chosen (g : GL (Fin 2) F) :
    v ((g : Matrix (Fin 2) (Fin 2) F) 1 (chosenCol v g)) = bottomVal v g := by
  unfold chosenCol bottomVal
  split_ifs with h
  · simp [max_eq_left h]
  · simp [max_eq_right (not_le.mp h).le]

private theorem bottomVal_ne_zero (g : GL (Fin 2) F) : bottomVal v g ≠ 0 := by
  unfold bottomVal
  intro h
  have h0 : v ((g : Matrix (Fin 2) (Fin 2) F) 1 0) = 0 := le_antisymm (h ▸ le_max_left _ _) zero_le'
  have h1 : v ((g : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := le_antisymm (h ▸ le_max_right _ _) zero_le'
  rw [map_eq_zero] at h0 h1
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero g
  rw [Matrix.det_fin_two, h0, h1] at hdet
  simp at hdet

private theorem chosen_ne_zero (g : GL (Fin 2) F) : (g : Matrix (Fin 2) (Fin 2) F) 1 (chosenCol v g) ≠ 0 := by
  intro h
  apply bottomVal_ne_zero v g
  rw [← val_chosen, h, map_zero]

private theorem localW_diagZ (ψ : F → ℂ) (hψ0 : ψ 0 = 1) (c : ℤ → ℂ) (om : ℂ) (π : F) (hπ0 : π ≠ 0)
    (hπ : v π = WithZero.exp (-1 : ℤ)) (m : ℤ) : localW v ψ c om (diagZ π hπ0 m) = c m := by
  have hcol : chosenCol v (diagZ π hπ0 m) = 1 := by
    simp [chosenCol, coe_diagZ]
  have hbv : bottomVal v (diagZ π hπ0 m) = 1 := by
    simp [bottomVal, coe_diagZ]
  simp only [localW, unipCoord, hcol, coe_diagZ, torusIndex, detOrd, bottomOrd, hbv]
  rw [Matrix.det_fin_two_of]
  simp [hψ0, map_zpow₀, hπ, ← WithZero.exp_zsmul]

end Invariants

section Laws

variable (v : Valuation F ℤᵐ⁰) (ψ : F → ℂ) (c : ℤ → ℂ) (om : ℂ)

private theorem localW_unipotent_mul (hψ : ∀ a b : F, ψ (a + b) = ψ a * ψ b) (y : F) (g : GL (Fin 2) F) :
    localW v ψ c om (unipotent y * g) = ψ y * localW v ψ c om g := by
  have hne := chosen_ne_zero v g
  have hmat : ((unipotent y * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = !![(g : Matrix (Fin 2) (Fin 2) F) 0 0 + y * (g : Matrix (Fin 2) (Fin 2) F) 1 0,
           (g : Matrix (Fin 2) (Fin 2) F) 0 1 + y * (g : Matrix (Fin 2) (Fin 2) F) 1 1;
           (g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 1 1] := by
    rw [Units.val_mul, coe_unipotent]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hcol : chosenCol v (unipotent y * g) = chosenCol v g := by
    simp only [chosenCol, hmat]; rfl
  have hbv : bottomVal v (unipotent y * g) = bottomVal v g := by
    simp only [bottomVal, hmat]; rfl
  have hdet : ((unipotent y * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det
      = (g : Matrix (Fin 2) (Fin 2) F).det := by
    rw [hmat, Matrix.det_fin_two_of, Matrix.det_fin_two]; ring
  have hcoord : unipCoord v (unipotent y * g) = y + unipCoord v g := by
    unfold unipCoord
    rw [hcol, hmat]
    rcases Fin.exists_fin_two.mp ⟨chosenCol v g, rfl⟩ with h | h <;> rw [h] at hne ⊢ <;>
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      field_simp <;> ring
  simp only [localW, hcoord, torusIndex, detOrd, bottomOrd, hdet, hbv, hψ]
  ring

private theorem localW_scalarPi_mul (hom : om ≠ 0) (π : F) (hπ0 : π ≠ 0) (hπ : v π = WithZero.exp (-1 : ℤ))
    (g : GL (Fin 2) F) : localW v ψ c om (scalarPi π hπ0 * g) = om * localW v ψ c om g := by
  set A := (g : Matrix (Fin 2) (Fin 2) F) with hA
  have hmat : ((scalarPi π hπ0 * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = !![π * A 0 0, π * A 0 1; π * A 1 0, π * A 1 1] := by
    rw [Units.val_mul, coe_scalarPi]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hA]
  have hvπ : v π ≠ 0 := by rw [hπ]; exact WithZero.exp_ne_zero
  have hle : ∀ a b : F, v (π * a) ≤ v (π * b) ↔ v a ≤ v b := by
    intro a b
    rw [map_mul, map_mul]
    exact mul_le_mul_iff_of_pos_left (lt_of_le_of_ne zero_le' hvπ.symm)
  have hcol : chosenCol v (scalarPi π hπ0 * g) = chosenCol v g := by
    simp only [chosenCol, hmat, hA, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, hle]
  have hbv : bottomVal v (scalarPi π hπ0 * g) = v π * bottomVal v g := by
    simp only [bottomVal, hmat, hA, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rcases le_total (v (A 1 0)) (v (A 1 1)) with h | h
    · rw [max_eq_right h, max_eq_right ((hle _ _).mpr h), map_mul]
    · rw [max_eq_left h, max_eq_left ((hle _ _).mpr h), map_mul]
  have hdet : ((scalarPi π hπ0 * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = π ^ 2 * A.det := by
    rw [hmat, Matrix.det_fin_two_of, Matrix.det_fin_two]; ring
  have hbo : bottomOrd v (scalarPi π hπ0 * g) = bottomOrd v g + 1 := by
    unfold bottomOrd
    rw [hbv, WithZero.log_mul hvπ (bottomVal_ne_zero v g), hπ, WithZero.log_exp]; ring
  have hdo : detOrd v (scalarPi π hπ0 * g) = detOrd v g + 2 := by
    unfold detOrd
    have hdet0 : v A.det ≠ 0 := (Valuation.ne_zero_iff v).mpr (Matrix.GeneralLinearGroup.det_ne_zero g)
    rw [hdet, map_mul, map_pow, hπ, WithZero.log_mul (pow_ne_zero 2 WithZero.exp_ne_zero) hdet0,
      ← WithZero.exp_nsmul, WithZero.log_exp]
    simp; ring
  have hcoord : unipCoord v (scalarPi π hπ0 * g) = unipCoord v g := by
    unfold unipCoord
    rw [hcol, hmat]
    rcases Fin.exists_fin_two.mp ⟨chosenCol v g, rfl⟩ with h | h <;> rw [h] <;>
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      rw [mul_div_mul_left _ _ hπ0]
  simp only [localW, hcoord, torusIndex, hdo, hbo]
  rw [show detOrd v g + 2 - 2 * (bottomOrd v g + 1) = detOrd v g - 2 * bottomOrd v g by ring, zpow_add_one₀ hom]
  ring

section Integral

private def IsIntegral (K : GL (Fin 2) F) : Prop := ∀ i j : Fin 2, v ((K : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1

private theorem isIntegral_map (k : GL (Fin 2) v.integer) :
    IsIntegral v (GeneralLinearGroup.map v.integer.subtype k) := by
  intro i j
  have : ((GeneralLinearGroup.map v.integer.subtype k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j
      = ((k : Matrix (Fin 2) (Fin 2) v.integer) i j : F) := by
    simp [GeneralLinearGroup.map, Units.coe_map, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [this]
  exact ((k : Matrix (Fin 2) (Fin 2) v.integer) i j).2

variable {v} {K : GL (Fin 2) F}

private theorem IsIntegral.bottomVal_mul_le (hK : IsIntegral v K) (g : GL (Fin 2) F) :
    bottomVal v (g * K) ≤ bottomVal v g := by
  unfold bottomVal
  rw [Units.val_mul]
  refine max_le ?_ ?_ <;>
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine (Valuation.map_add v _ _).trans (max_le_max ?_ ?_) <;>
    · rw [map_mul]
      exact mul_le_of_le_one_right' (hK _ _)

private theorem IsIntegral.bottomVal_mul (hK : IsIntegral v K) (hK' : IsIntegral v K⁻¹) (g : GL (Fin 2) F) :
    bottomVal v (g * K) = bottomVal v g := by
  refine le_antisymm (hK.bottomVal_mul_le g) ?_
  have h := hK'.bottomVal_mul_le (g * K)
  rwa [mul_inv_cancel_right] at h

private theorem IsIntegral.val_det_le_one (hK : IsIntegral v K) : v ((K : Matrix (Fin 2) (Fin 2) F).det) ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (Valuation.map_sub v _ _).trans (max_le ?_ ?_) <;>
  · rw [map_mul]
    exact mul_le_one' (hK _ _) (hK _ _)

private theorem IsIntegral.val_det (hK : IsIntegral v K) (hK' : IsIntegral v K⁻¹) :
    v ((K : Matrix (Fin 2) (Fin 2) F).det) = 1 := by
  have hprod : v ((K : Matrix (Fin 2) (Fin 2) F).det)
      * v ((K⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm hK.val_det_le_one ?_
  calc (1 : ℤᵐ⁰) = _ := hprod.symm
    _ ≤ v ((K : Matrix (Fin 2) (Fin 2) F).det) * 1 := mul_le_mul' le_rfl hK'.val_det_le_one
    _ = _ := mul_one _

private theorem IsIntegral.detOrd_mul (hK : IsIntegral v K) (hK' : IsIntegral v K⁻¹) (g : GL (Fin 2) F) :
    detOrd v (g * K) = detOrd v g := by
  unfold detOrd
  rw [Units.val_mul, Matrix.det_mul, map_mul, hK.val_det hK', mul_one]

private theorem IsIntegral.torusIndex_mul (hK : IsIntegral v K) (hK' : IsIntegral v K⁻¹) (g : GL (Fin 2) F) :
    torusIndex v (g * K) = torusIndex v g := by
  unfold torusIndex bottomOrd
  rw [hK.detOrd_mul hK', hK.bottomVal_mul hK']

private theorem IsIntegral.val_unipCoord_mul_sub (hK : IsIntegral v K) (hK' : IsIntegral v K⁻¹) (g : GL (Fin 2) F) :
    v (unipCoord v (g * K) - unipCoord v g) ≤ WithZero.exp (-torusIndex v g) := by
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 2) (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) = A := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) F, (K : Matrix (Fin 2) (Fin 2) F) = M := ⟨_, rfl⟩
  have hKM : ∀ i j, v (M i j) ≤ 1 := by intro i j; rw [← hM]; exact hK i j
  have hmul : ((g * K : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = A * M := by rw [Units.val_mul, hA, hM]
  have he : v (A 1 (chosenCol v g)) = bottomVal v g := by rw [← hA]; exact val_chosen v g
  have he' : v ((A * M) 1 (chosenCol v (g * K))) = bottomVal v g := by
    rw [← hmul, val_chosen, hK.bottomVal_mul hK']
  have hB : bottomVal v g ≠ 0 := bottomVal_ne_zero v g
  have hdet : v A.det ≠ 0 := by
    rw [← hA]; exact (Valuation.ne_zero_iff v).mpr (Matrix.GeneralLinearGroup.det_ne_zero g)
  have hez : A 1 (chosenCol v g) ≠ 0 := by rw [← hA]; exact chosen_ne_zero v g
  have hez' : (A * M) 1 (chosenCol v (g * K)) ≠ 0 := by rw [← hmul]; exact chosen_ne_zero v (g * K)

  have hnum : ∀ j j' : Fin 2, ∃ t : F, v t ≤ 1 ∧
      ((A * M) 0 j' * A 1 j - (A * M) 1 j' * A 0 j = t * A.det ∨
        (A * M) 0 j' * A 1 j - (A * M) 1 j' * A 0 j = -(t * A.det)) := by
    intro j j'
    fin_cases j <;> fin_cases j' <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    · exact ⟨M 1 0, hKM 1 0, Or.inr (by ring)⟩
    · exact ⟨M 1 1, hKM 1 1, Or.inr (by ring)⟩
    · exact ⟨M 0 0, hKM 0 0, Or.inl (by ring)⟩
    · exact ⟨M 0 1, hKM 0 1, Or.inl (by ring)⟩
  have hdiff : unipCoord v (g * K) - unipCoord v g
      = ((A * M) 0 (chosenCol v (g * K)) * A 1 (chosenCol v g) - (A * M) 1 (chosenCol v (g * K)) * A 0 (chosenCol v g))
          / ((A * M) 1 (chosenCol v (g * K)) * A 1 (chosenCol v g)) := by
    unfold unipCoord
    rw [hmul, hA, div_sub_div _ _ hez' hez]
  obtain ⟨t, ht, hN⟩ := hnum (chosenCol v g) (chosenCol v (g * K))
  have hvN : v ((A * M) 0 (chosenCol v (g * K)) * A 1 (chosenCol v g)
      - (A * M) 1 (chosenCol v (g * K)) * A 0 (chosenCol v g)) ≤ v A.det := by
    rcases hN with h | h
    · rw [h, map_mul]; exact mul_le_of_le_one_left' ht
    · rw [h, Valuation.map_neg, map_mul]; exact mul_le_of_le_one_left' ht
  have hexp : WithZero.exp (-torusIndex v g) = v A.det * (bottomVal v g)⁻¹ * (bottomVal v g)⁻¹ := by
    have hint : -torusIndex v g
        = WithZero.log (v A.det) + -WithZero.log (bottomVal v g) + -WithZero.log (bottomVal v g) := by
      unfold torusIndex detOrd bottomOrd; rw [hA]; ring
    rw [hint, WithZero.exp_add, WithZero.exp_add, WithZero.exp_neg, WithZero.exp_log hdet, WithZero.exp_log hB]
  rw [hdiff, map_div₀, map_mul, he', he, hexp, div_eq_mul_inv, mul_inv, ← mul_assoc]
  exact mul_le_mul' (mul_le_mul' hvN le_rfl) le_rfl

variable (v) in

private theorem IsIntegral.localW_mul (hK : IsIntegral v K) (hK' : IsIntegral v K⁻¹)
    (hψ : ∀ a b : F, ψ (a + b) = ψ a * ψ b) (ℓ : ℤ)
    (hψℓ : ∀ y : F, v y ≤ WithZero.exp ℓ → ψ y = 1) (hc : ∀ m : ℤ, m < -ℓ → c m = 0) (g : GL (Fin 2) F) :
    localW v ψ c om (g * K) = localW v ψ c om g := by
  unfold localW
  rw [hK.torusIndex_mul hK', bottomOrd, hK.bottomVal_mul hK', ← bottomOrd]
  by_cases hm : torusIndex v g < -ℓ
  · rw [hc _ hm]; ring
  · rw [not_lt] at hm
    congr 2
    have hsub := hK.val_unipCoord_mul_sub hK' g
    have hle : WithZero.exp (-torusIndex v g) ≤ WithZero.exp ℓ := by
      rw [WithZero.exp_le_exp]; linarith
    have h1 : ψ (unipCoord v (g * K) - unipCoord v g) = 1 := hψℓ _ (hsub.trans hle)
    calc ψ (unipCoord v (g * K))
        = ψ (unipCoord v g + (unipCoord v (g * K) - unipCoord v g)) := by ring_nf
      _ = ψ (unipCoord v g) := by rw [hψ, h1, mul_one]

variable (v) in

private theorem localW_mul_map (hψ : ∀ a b : F, ψ (a + b) = ψ a * ψ b) (ℓ : ℤ)
    (hψℓ : ∀ y : F, v y ≤ WithZero.exp ℓ → ψ y = 1) (hc : ∀ m : ℤ, m < -ℓ → c m = 0) (g : GL (Fin 2) F)
    (k : GL (Fin 2) v.integer) :
    localW v ψ c om (g * GeneralLinearGroup.map v.integer.subtype k) = localW v ψ c om g :=
  (isIntegral_map v k).localW_mul v ψ c om
    (by
      rw [← map_inv (GeneralLinearGroup.map v.integer.subtype : GL (Fin 2) v.integer →* GL (Fin 2) F) k]
      exact isIntegral_map v k⁻¹)
    hψ ℓ hψℓ hc g

end Integral

end Laws

section Hecke

variable (v : Valuation F ℤᵐ⁰) (ψ : F → ℂ) (c : ℤ → ℂ) (om : ℂ) (π : F) (hπ0 : π ≠ 0)

private def repSome (β : F) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![π, β; 0, 1] (by simp [det_fin_two_of, hπ0])

private def repInf : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, π] (by simp [det_fin_two_of, hπ0])

private def torusElt (y : F) (m n : ℤ) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![π ^ m * π ^ n, y * π ^ n; 0, π ^ n]
    (by simp [det_fin_two_of, zpow_ne_zero m hπ0, zpow_ne_zero n hπ0])

private theorem coe_torusElt (y : F) (m n : ℤ) :
    ((torusElt π hπ0 y m n : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![π ^ m * π ^ n, y * π ^ n; 0, π ^ n] := rfl

private theorem torusElt_mul_repSome (y : F) (m n : ℤ) (β : F) :
    torusElt π hπ0 y m n * repSome π hπ0 β = torusElt π hπ0 (y + π ^ m * β) (m + 1) n := by
  ext i j
  rw [Units.val_mul, coe_torusElt, coe_torusElt]
  fin_cases i <;> fin_cases j <;>
    simp [repSome, Matrix.mul_apply, Fin.sum_univ_two, zpow_add_one₀ hπ0] <;> ring

private theorem torusElt_mul_repInf (y : F) (m n : ℤ) :
    torusElt π hπ0 y m n * repInf π hπ0 = torusElt π hπ0 y (m - 1) (n + 1) := by
  ext i j
  rw [Units.val_mul, coe_torusElt, coe_torusElt]
  fin_cases i <;> fin_cases j <;>
    simp [repInf, Matrix.mul_apply, Fin.sum_univ_two, zpow_add_one₀ hπ0, zpow_sub_one₀ hπ0] <;>
    field_simp

variable (hπ : v π = WithZero.exp (-1 : ℤ))
include hπ

private theorem val_zpow (n : ℤ) : v (π ^ n) = WithZero.exp (-n) := by
  rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]; simp

private theorem localW_torusElt (y : F) (m n : ℤ) :
    localW v ψ c om (torusElt π hπ0 y m n) = ψ y * c m * om ^ n := by
  have hn : π ^ n ≠ 0 := zpow_ne_zero n hπ0
  have hcol : chosenCol v (torusElt π hπ0 y m n) = 1 := by
    simp only [chosenCol, coe_torusElt, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, map_zero]
    rw [if_neg]
    rw [not_le]
    exact lt_of_le_of_ne zero_le' (((Valuation.ne_zero_iff v).mpr hn)).symm
  have hbv : bottomVal v (torusElt π hπ0 y m n) = WithZero.exp (-n) := by
    simp only [bottomVal, coe_torusElt, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, map_zero]
    simp only [val_zpow v π hπ]
    exact max_eq_right zero_le'
  have hdet : ((torusElt π hπ0 y m n : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = π ^ (m + n + n) := by
    rw [coe_torusElt, Matrix.det_fin_two_of, zpow_add₀ hπ0, zpow_add₀ hπ0]; ring
  have hcoord : unipCoord v (torusElt π hπ0 y m n) = y := by
    simp only [unipCoord, hcol, coe_torusElt, Matrix.of_apply, Matrix.cons_val_one]
    exact mul_div_cancel_right₀ y hn
  simp only [localW, hcoord, torusIndex, detOrd, bottomOrd, hdet, hbv, val_zpow v π hπ, WithZero.log_exp]
  congr 2 <;> ring

private theorem hecke_identity_torusElt (hom : om ≠ 0) (ℓ : ℤ) (Nc lam : ℂ) (B : Finset F)
    (hψ : ∀ a b : F, ψ (a + b) = ψ a * ψ b) (hψℓ : ∀ y : F, v y ≤ WithZero.exp ℓ → ψ y = 1)
    (hBint : ∀ β ∈ B, v β ≤ 1) (hcard : (B.card : ℂ) = Nc)
    (hsum0 : ∑ β ∈ B, ψ (π ^ (-ℓ - 1) * β) = 0)
    (hc0 : ∀ m : ℤ, m < -ℓ → c m = 0)
    (hrec : ∀ m : ℤ, -ℓ ≤ m → Nc * c (m + 1) + om * c (m - 1) = lam * c m)
    (y : F) (m n : ℤ) :
    ∑ β ∈ B, localW v ψ c om (torusElt π hπ0 y m n * repSome π hπ0 β)
        + localW v ψ c om (torusElt π hπ0 y m n * repInf π hπ0)
      = lam * localW v ψ c om (torusElt π hπ0 y m n) := by
  simp only [torusElt_mul_repSome, torusElt_mul_repInf, localW_torusElt v ψ c om π hπ0 hπ, hψ, zpow_add_one₀ hom]
  by_cases hm : -ℓ ≤ m
  ·
    have h1 : ∀ β ∈ B, ψ (π ^ m * β) = 1 := by
      intro β hβ
      apply hψℓ
      rw [map_mul, val_zpow v π hπ]
      calc WithZero.exp (-m) * v β ≤ WithZero.exp (-m) * 1 := mul_le_mul' le_rfl (hBint β hβ)
        _ = WithZero.exp (-m) := mul_one _
        _ ≤ WithZero.exp ℓ := by rw [WithZero.exp_le_exp]; linarith
    rw [Finset.sum_congr rfl (fun β hβ => by rw [h1 β hβ]), Finset.sum_const, nsmul_eq_mul, hcard]
    linear_combination (ψ y * om ^ n) * hrec m hm
  · rw [not_le] at hm
    have hcm : c m = 0 := hc0 m hm
    have hcm' : c (m - 1) = 0 := hc0 _ (by omega)
    by_cases hm' : m = -ℓ - 1
    ·
      subst hm'
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, hsum0]
      simp [hcm, hcm']
    ·
      have hcm1 : c (m + 1) = 0 := hc0 _ (by omega)
      simp [hcm, hcm', hcm1]

end Hecke

end LocalWhittaker

open scoped WithZero nonZeroDivisors

namespace FiniteWhittaker
namespace Generic

section Finprod

variable {ι : Type*} [DecidableEq ι]

private theorem finprod_update_mul {f : ι → ℂ} (hf : (Function.mulSupport f).Finite) (i₀ : ι) (a : ℂ) :
    ∏ᶠ i, Function.update f i₀ (a * f i₀) i = a * ∏ᶠ i, f i := by
  set T : Finset ι := insert i₀ hf.toFinset with hT
  have hi₀ : i₀ ∈ T := Finset.mem_insert_self _ _
  have h2 : Function.mulSupport f ⊆ T := fun i hi =>
    Finset.mem_insert_of_mem (hf.mem_toFinset.mpr hi)
  have h1 : Function.mulSupport (Function.update f i₀ (a * f i₀)) ⊆ T := by
    intro i hi
    by_cases h : i = i₀
    · subst h; exact hi₀
    · rw [Function.mem_mulSupport, Function.update_of_ne h] at hi
      exact h2 hi
  rw [finprod_eq_prod_of_mulSupport_subset _ h1, finprod_eq_prod_of_mulSupport_subset _ h2,
    Finset.prod_update_of_mem hi₀, Finset.sdiff_singleton_eq_erase, ← Finset.mul_prod_erase T f hi₀]
  ring

private theorem finprod_eq_mul_finprod_update_one {f : ι → ℂ} (hf : (Function.mulSupport f).Finite) (i₀ : ι) :
    ∏ᶠ i, f i = f i₀ * ∏ᶠ i, Function.update f i₀ 1 i := by
  set T : Finset ι := insert i₀ hf.toFinset with hT
  have hi₀ : i₀ ∈ T := Finset.mem_insert_self _ _
  have h2 : Function.mulSupport f ⊆ T := fun i hi =>
    Finset.mem_insert_of_mem (hf.mem_toFinset.mpr hi)
  have h1 : Function.mulSupport (Function.update f i₀ 1) ⊆ T := by
    intro i hi
    by_cases h : i = i₀
    · subst h; exact hi₀
    · rw [Function.mem_mulSupport, Function.update_of_ne h] at hi
      exact h2 hi
  rw [finprod_eq_prod_of_mulSupport_subset _ h1, finprod_eq_prod_of_mulSupport_subset _ h2,
    Finset.prod_update_of_mem hi₀, Finset.sdiff_singleton_eq_erase, one_mul, Finset.mul_prod_erase T f hi₀]

end Finprod

private theorem mulSupport_finite_of_eventually
    {ι : Type*} {f : ι → ℂ} {p : ι → Prop} (hp : ∀ᶠ i in Filter.cofinite, p i)
    (hf : ∀ i, p i → f i = 1) : (Function.mulSupport f).Finite := by
  refine (Filter.eventually_cofinite.mp hp).subset ?_
  intro i hi hpi
  exact hi (hf i hpi)

private theorem sum_eq_zero_of_mul_of_ne_one {Q : Type*} [AddGroup Q] [Fintype Q] (χ : Q → ℂ)
    (hmul : ∀ a b : Q, χ (a + b) = χ a * χ b) (hne : ∃ a : Q, χ a ≠ 1) : ∑ a, χ a = 0 := by
  obtain ⟨a₀, ha₀⟩ := hne
  have h : ∑ a, χ a = χ a₀ * ∑ a, χ a := by
    rw [Finset.mul_sum]
    calc ∑ a, χ a = ∑ a, χ (a + a₀) := (Fintype.sum_equiv (Equiv.addRight a₀) _ _ (fun _ => rfl)).symm
      _ = ∑ a, χ a₀ * χ a := by simp only [hmul, mul_comm]
  have h' : (χ a₀ - 1) * ∑ a, χ a = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) ha₀
  · exact h0

section AE

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

private theorem eventually_forall_apply_mem_integers (A : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) :
    ∀ᶠ w : HeightOneSpectrum R in Filter.cofinite,
      ∀ i j : Fin 2, A i j w ∈ w.adicCompletionIntegers K := by
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  exact (A i j).2

private theorem eventually_level_eq_zero (I : FractionalIdeal R⁰ K) (ℓ : HeightOneSpectrum R → ℤ)
    (hℓ : ∀ w, ℓ w = FractionalIdeal.count K w I) :
    ∀ᶠ w : HeightOneSpectrum R in Filter.cofinite, ℓ w = 0 :=
  (FractionalIdeal.finite_factors I).mono fun w hw => by rw [hℓ w, hw]

end AE

section Approx

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

private theorem exists_global_sub_mem_of_approx (v : HeightOneSpectrum R)
    (happrox : ∀ a : FiniteAdeleRing R K, ∃ x : K, ∀ w : HeightOneSpectrum R,
      a w - algebraMap K (w.adicCompletion K) x ∈ w.adicCompletionIntegers K)
    (single : v.adicCompletion K → FiniteAdeleRing R K)
    (hsingle_self : ∀ y, single y v = y)
    (hsingle_ne : ∀ y (w : HeightOneSpectrum R), w ≠ v → single y w = 0)
    (y : v.adicCompletion K) (hy : y ∈ v.adicCompletionIntegers K) :
    ∃ z : R, Valued.v (y - algebraMap R (v.adicCompletion K) z) ≤ WithZero.exp (-1 : ℤ) := by

  obtain ⟨t, ht⟩ := v.intValuation_exists_uniformizer
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at ht
    exact WithZero.exp_ne_zero ht.symm
  have htK : (algebraMap R K t : K) ≠ 0 := by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]
  have htv : Valued.v (algebraMap R (v.adicCompletion K) t) = WithZero.exp (-1 : ℤ) := by
    rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap, ht]
  have htv0 : (algebraMap R (v.adicCompletion K) t) ≠ 0 := by
    intro h; rw [h, map_zero] at htv; exact WithZero.exp_ne_zero htv.symm

  set T : v.adicCompletion K := algebraMap R (v.adicCompletion K) t with hTdef
  obtain ⟨x, hx⟩ := happrox (single (y / T))

  have hxv : Valued.v (y / T - algebraMap K (v.adicCompletion K) x) ≤ 1 := by
    have := hx v
    rwa [hsingle_self, mem_adicCompletionIntegers] at this
  have hkey : Valued.v (y - T * algebraMap K (v.adicCompletion K) x) ≤ WithZero.exp (-1 : ℤ) := by
    have h1 : y - T * algebraMap K (v.adicCompletion K) x = T * (y / T - algebraMap K (v.adicCompletion K) x) := by
      field_simp
    rw [h1, map_mul, htv]
    exact mul_le_of_le_one_right' hxv

  have htower : ∀ (w : HeightOneSpectrum R) (r : R),
      algebraMap K (w.adicCompletion K) (algebraMap R K r) = algebraMap R (w.adicCompletion K) r :=
    fun w r => (IsScalarTower.algebraMap_apply R K (w.adicCompletion K) r).symm
  have hb : ∀ (w : HeightOneSpectrum R) (k : K),
      Valued.v (algebraMap K (w.adicCompletion K) k) = w.valuation K k :=
    fun w k => valuedAdicCompletion_eq_valuation' w k
  have hint : ∀ w : HeightOneSpectrum R, w.valuation K (algebraMap R K t * x) ≤ 1 := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [← hb w, map_mul, htower]

      have h2 : T * algebraMap K (w.adicCompletion K) x
          = y - (y - T * algebraMap K (w.adicCompletion K) x) := by ring
      rw [h2]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · exact (mem_adicCompletionIntegers R K w).mp hy
      · exact hkey.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
    · have h0 := hx w
      rw [hsingle_ne _ w hw, zero_sub, mem_adicCompletionIntegers, Valuation.map_neg, hb w] at h0
      rw [map_mul]
      exact mul_le_one' (valuation_le_one w t) h0
  obtain ⟨z, hz⟩ := mem_integers_of_valuation_le_one (R := R) (K := K) (x := algebraMap R K t * x) hint
  refine ⟨z, ?_⟩
  have h3 : algebraMap R (v.adicCompletion K) z = T * algebraMap K (v.adicCompletion K) x := by
    rw [← htower v z, hz, map_mul, htower]
  rw [h3]
  exact hkey

end Approx

end FiniteWhittaker.Generic

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm
open AdelicDock LocalGL2 UnramifiedWhittaker LanglandsTunnell.Converse LocalWhittaker FiniteWhittaker.Generic
open scoped WithZero Classical

namespace FiniteWhittaker

variable {K : Type} [Field K] [NumberField K]

private scoped instance residueFinite (v : HeightOneSpectrum (𝓞 K)) : Finite (𝓞 K ⧸ v.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot

private noncomputable scoped instance residueFintype (v : HeightOneSpectrum (𝓞 K)) : Fintype (𝓞 K ⧸ v.asIdeal) :=
  Fintype.ofFinite _

section Pieces

variable {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι : Type*} {reps : ι → G}

private theorem isHeckeCosetSystem_mul_left (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) {u : G}
    (hu : u ∈ U) : HeckeIntegralSeam.IsHeckeCosetSystem U g (fun i => u * reps i) where
  mem_doubleCoset i := HeckePair.mul_mem_doubleCoset (hsys.mem_doubleCoset i) hu
  covers x hx := by
    obtain ⟨i, hi⟩ := hsys.covers (u⁻¹ * x) (HeckePair.mul_mem_doubleCoset hx (inv_mem hu))
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    simpa [mul_assoc] using hi
  mk_injective i j hij := by
    apply hsys.mk_injective
    simp only at hij ⊢
    rw [QuotientGroup.eq] at hij ⊢
    simpa [mul_assoc] using hij

private theorem isHeckeCosetSystem_comp_equiv (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) {κ : Type*}
    (e : κ ≃ ι) : HeckeIntegralSeam.IsHeckeCosetSystem U g (fun i => reps (e i)) where
  mem_doubleCoset i := hsys.mem_doubleCoset (e i)
  covers x hx := by
    obtain ⟨i, hi⟩ := hsys.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  mk_injective i j hij := e.injective (hsys.mk_injective hij)

private theorem torusFactor_natCast (N lam om : ℂ) (n : ℕ) :
    torusFactor N lam om n = heckeRecursionSeq N lam om n := by
  simp [torusFactor]

private theorem torusFactor_of_neg (N lam om : ℂ) {m : ℤ} (hm : m < 0) : torusFactor N lam om m = 0 := by
  simp [torusFactor, not_le.mpr hm]

private theorem torusFactor_shift_eq_zero (N lam om : ℂ) (ℓ m : ℤ) (hm : m < -ℓ) :
    torusFactor N lam om (m + ℓ) = 0 :=
  torusFactor_of_neg N lam om (by omega)

private theorem torusFactor_shift_rec (N lam om : ℂ) (hN : N ≠ 0) (ℓ m : ℤ) (hm : -ℓ ≤ m) :
    N * torusFactor N lam om (m + 1 + ℓ) + om * torusFactor N lam om (m - 1 + ℓ)
      = lam * torusFactor N lam om (m + ℓ) := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, m + ℓ = j := ⟨(m + ℓ).toNat, by omega⟩
  have h1 : m + 1 + ℓ = ((j + 1 : ℕ) : ℤ) := by push_cast; omega
  rw [h1, hj, torusFactor_natCast, torusFactor_natCast]
  rcases j with _ | j
  · rw [torusFactor_of_neg N lam om (by omega)]
    simp only [heckeRecursionSeq, mul_zero, add_zero, mul_one]
    field_simp
  · have h3 : m - 1 + ℓ = (j : ℤ) := by omega
    rw [h3, torusFactor_natCast]
    show N * heckeRecursionSeq N lam om (j + 2) + om * heckeRecursionSeq N lam om j
      = lam * heckeRecursionSeq N lam om (j + 1)
    rw [heckeRecursionSeq]
    field_simp
    ring

end Pieces

private structure PlaceData (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) where
  ϖ : v.adicCompletionIntegers K
  hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0
  hval : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ)
  hgen : finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (diagPi ϖ hϖ0)) = heckeGen (𝓞 K) K v
  sec : 𝓞 K ⧸ v.asIdeal → 𝓞 K
  hsec : ∀ c : 𝓞 K ⧸ v.asIdeal, Ideal.Quotient.mk v.asIdeal (sec c) = c
  hsys : ∀ M : Ideal (𝓞 K), ¬ v.asIdeal ∣ M →
    HeckeIntegralSeam.IsHeckeCosetSystem (levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
      (heckeGen (𝓞 K) K v)
      (fun i : Option (𝓞 K ⧸ v.asIdeal) =>
        finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v
          (i.elim (localRepInf ϖ hϖ0)
            (fun c => localRepSome ϖ hϖ0 (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c))))))

private theorem nonempty_placeData (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (PlaceData K v) := by
  obtain ⟨ϖ, hϖ0, hval, hgen, sec, hsec, hsys⟩ :=
    HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen K v
  exact ⟨⟨ϖ, hϖ0, hval, hgen, sec, hsec, hsys⟩⟩

private def pd (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : PlaceData K v :=
  Classical.choice (nonempty_placeData K v)

variable (K)

private def unif (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K := ((pd K v).ϖ : v.adicCompletion K)

private theorem unif_ne_zero (v : HeightOneSpectrum (𝓞 K)) : unif K v ≠ 0 := (pd K v).hϖ0

private theorem valued_unif (v : HeightOneSpectrum (𝓞 K)) : Valued.v (unif K v) = WithZero.exp (-1 : ℤ) :=
  (pd K v).hval

private def lvl
    (v : HeightOneSpectrum (𝓞 K)) : ℤ := LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal K v)

variable {K}

private def cseq (Pi : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K)) (k : ℤ) : ℂ :=
  torusFactor (HeckeEigensystem.cNorm v) (Pi.a v) (Pi.toRawCentral.b v) (k + lvl K v)

private def Wloc (Pi : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (v.adicCompletion K)) : ℂ :=
  localW Valued.v (StandardAddChar.psiLocal K v) (cseq Pi v) (Pi.toRawCentral.b v) h

private def compAt (w : HeightOneSpectrum (𝓞 K)) : AdelicGL2 (𝓞 K) K →* GL (Fin 2) (w.adicCompletion K) :=
  (finComponent (𝓞 K) K w).comp (glFin (𝓞 K) K)

private theorem compAt_apply (w : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (compAt w g : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j
      = (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w := rfl

private theorem compAt_placeEmbed_self (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (v.adicCompletion K)) :
    compAt v (placeEmbed K v h) = h := by
  show finComponent (𝓞 K) K v (glFin (𝓞 K) K (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v h))) = h
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem compAt_placeEmbed_of_ne
    {v w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) (h : GL (Fin 2) (v.adicCompletion K)) :
    compAt w (placeEmbed K v h) = 1 := by
  show finComponent (𝓞 K) K w (glFin (𝓞 K) K (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v h))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

private def factor (S : Finset (HeightOneSpectrum (𝓞 K))) (Pi : HeckeEigensystem K ℂ) (g : AdelicGL2 (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if w ∈ S then 1 else Wloc Pi w (compAt w g)

private def WfFun (S : Finset (HeightOneSpectrum (𝓞 K))) (Pi : HeckeEigensystem K ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∏ᶠ w, factor S Pi g w

section LocalLaws

variable (Pi : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K))

private theorem psi_add (a b : v.adicCompletion K) :
    StandardAddChar.psiLocal K v (a + b) = StandardAddChar.psiLocal K v a * StandardAddChar.psiLocal K v b :=
  AddChar.map_add_eq_mul _ a b

private theorem level_law :
    (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (lvl K v) → StandardAddChar.psiLocal K v x = 1) ∧
      ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (lvl K v + 1) ∧ StandardAddChar.psiLocal K v x ≠ 1 :=
  LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel K v _
    ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v x
      (by rwa [mem_adicCompletionIntegers, ← WithZero.exp_zero])⟩
    (LanglandsTunnell.TateLocal.psiLocal_ne_one K v)

private theorem cseq_eq_zero {m : ℤ} (hm : m < -lvl K v) : cseq Pi v m = 0 :=
  torusFactor_shift_eq_zero _ _ _ _ _ hm

private theorem cseq_zero_of_lvl_eq_zero (hv : lvl K v = 0) : cseq Pi v 0 = 1 := by
  simp [cseq, hv, torusFactor, heckeRecursionSeq]

private theorem cseq_neg_lvl : cseq Pi v (-lvl K v) = 1 := by
  simp [cseq, torusFactor, heckeRecursionSeq]

private theorem Wloc_unipotent_mul (x : v.adicCompletion K) (h : GL (Fin 2) (v.adicCompletion K)) :
    Wloc Pi v (LocalWhittaker.unipotent x * h) = StandardAddChar.psiLocal K v x * Wloc Pi v h :=
  localW_unipotent_mul _ _ _ _ (psi_add v) x h

private theorem Wloc_mul_of_isIntegral
    {k : GL (Fin 2) (v.adicCompletion K)} (hk : LocalWhittaker.IsIntegral Valued.v k)
    (hk' : LocalWhittaker.IsIntegral Valued.v k⁻¹) (h : GL (Fin 2) (v.adicCompletion K)) :
    Wloc Pi v (h * k) = Wloc Pi v h :=
  hk.localW_mul _ _ _ _ hk' (psi_add v) (lvl K v) (level_law v).1 (fun _ hm => cseq_eq_zero Pi v hm) h

private theorem Wloc_diagZ (m : ℤ) : Wloc Pi v (LocalWhittaker.diagZ (unif K v) (unif_ne_zero K v) m) = cseq Pi v m :=
  localW_diagZ _ _ (AddChar.map_zero_eq_one _) _ _ _ _ (valued_unif K v) m

private theorem Wloc_one_of_isIntegral_of_lvl
    {k : GL (Fin 2) (v.adicCompletion K)} (hk : LocalWhittaker.IsIntegral Valued.v k)
    (hk' : LocalWhittaker.IsIntegral Valued.v k⁻¹) (hv : lvl K v = 0) : Wloc Pi v k = 1 := by
  have h1 : LocalWhittaker.diagZ (unif K v) (unif_ne_zero K v) 0 = 1 := by
    refine Units.ext ?_
    rw [LocalWhittaker.coe_diagZ, zpow_zero, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [← one_mul k, Wloc_mul_of_isIntegral Pi v hk hk', ← h1, Wloc_diagZ, cseq_zero_of_lvl_eq_zero Pi v hv]

end LocalLaws

private theorem isIntegral_compAt_of_mem_integral {g : AdelicGL2 (𝓞 K) K} {w : HeightOneSpectrum (𝓞 K)}
    (hg : ∀ i j : Fin 2, (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w
      ∈ w.adicCompletionIntegers K) : LocalWhittaker.IsIntegral Valued.v (compAt w g) := fun i j => by
  rw [compAt_apply]
  exact (mem_adicCompletionIntegers _ _ _).mp (hg i j)

private theorem isIntegral_compAt_inv_of_mem_integral {g : AdelicGL2 (𝓞 K) K} {w : HeightOneSpectrum (𝓞 K)}
    (hg : ∀ i j : Fin 2, (glFin (𝓞 K) K g⁻¹ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j w
      ∈ w.adicCompletionIntegers K) : LocalWhittaker.IsIntegral Valued.v (compAt w g)⁻¹ := by
  rw [← map_inv]
  exact isIntegral_compAt_of_mem_integral hg

private theorem mulSupport_factor_finite (S : Finset (HeightOneSpectrum (𝓞 K))) (Pi : HeckeEigensystem K ℂ)
    (g : AdelicGL2 (𝓞 K) K) : (Function.mulSupport (factor S Pi g)).Finite := by
  have hA := eventually_forall_apply_mem_integers (R := 𝓞 K) (K := K)
    (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
  have hB := eventually_forall_apply_mem_integers (R := 𝓞 K) (K := K)
    (glFin (𝓞 K) K g⁻¹ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
  have hL := eventually_level_eq_zero (R := 𝓞 K) (K := K)
    (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) (lvl K)
    (fun w => LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal K w)
  refine mulSupport_finite_of_eventually ((hA.and hB).and hL) ?_
  rintro w ⟨⟨hw1, hw2⟩, hw3⟩
  unfold factor
  split_ifs with hS
  · rfl
  · exact Wloc_one_of_isIntegral_of_lvl Pi w (isIntegral_compAt_of_mem_integral (fun i j => hw1 i j))
      (isIntegral_compAt_inv_of_mem_integral (fun i j => hw2 i j)) hw3

section Fields

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (Pi : HeckeEigensystem K ℂ)

private theorem factor_congr {g g' : AdelicGL2 (𝓞 K) K} (h : glFin (𝓞 K) K g = glFin (𝓞 K) K g') :
    factor S Pi g = factor S Pi g' := by
  funext w
  unfold factor compAt
  simp only [MonoidHom.comp_apply, h]

private theorem WfFun_finite_dependent (g g' : AdelicGL2 (𝓞 K) K) (h : glFin (𝓞 K) K g = glFin (𝓞 K) K g') :
    WfFun S Pi g = WfFun S Pi g' := by
  unfold WfFun
  rw [factor_congr S Pi h]

private theorem factor_mul_placeEmbed (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (v.adicCompletion K))
    (g : AdelicGL2 (𝓞 K) K) {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    factor S Pi (g * placeEmbed K v h) w = factor S Pi g w := by
  unfold factor
  rw [map_mul, compAt_placeEmbed_of_ne hw, mul_one]

private theorem factor_placeEmbed_mul (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (v.adicCompletion K))
    (g : AdelicGL2 (𝓞 K) K) {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    factor S Pi (placeEmbed K v h * g) w = factor S Pi g w := by
  unfold factor
  rw [map_mul, compAt_placeEmbed_of_ne hw, one_mul]

private theorem WfFun_blind_at (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) (h : GL (Fin 2) (v.adicCompletion K))
    (g : AdelicGL2 (𝓞 K) K) : WfFun S Pi (g * placeEmbed K v h) = WfFun S Pi g := by
  unfold WfFun
  refine finprod_congr fun w => ?_
  by_cases hw : w = v
  · subst hw; simp [factor, hv]
  · exact factor_mul_placeEmbed S Pi v h g hw

private theorem factor_placeEmbed_mul_eq_update (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (h : GL (Fin 2) (v.adicCompletion K)) (g : AdelicGL2 (𝓞 K) K) (a : ℂ)
    (hval : Wloc Pi v (h * compAt v g) = a * Wloc Pi v (compAt v g)) :
    factor S Pi (placeEmbed K v h * g) = Function.update (factor S Pi g) v (a * factor S Pi g v) := by
  funext w
  by_cases hw : w = v
  · subst hw
    rw [Function.update_self]
    simp only [factor, hv, if_false, map_mul, compAt_placeEmbed_self]
    exact hval
  · rw [Function.update_of_ne hw, factor_placeEmbed_mul S Pi v h g hw]

private theorem WfFun_unipotent_left (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (x : v.adicCompletion K)
    (g : AdelicGL2 (𝓞 K) K) :
    WfFun S Pi (placeEmbed K v (UnramifiedWhittaker.unipotent x) * g)
      = StandardAddChar.psiLocal K v x * WfFun S Pi g := by
  have hu : UnramifiedWhittaker.unipotent x = LocalWhittaker.unipotent x := Units.ext rfl
  unfold WfFun
  rw [factor_placeEmbed_mul_eq_update S Pi v hv _ g (StandardAddChar.psiLocal K v x)
    (by rw [hu]; exact Wloc_unipotent_mul Pi v x _)]
  exact finprod_update_mul (mulSupport_factor_finite S Pi g) v _

private theorem WfFun_integral_right (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (k : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K) :
    WfFun S Pi (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k)) = WfFun S Pi g := by
  unfold WfFun
  refine finprod_congr fun w => ?_
  by_cases hw : w = v
  · subst hw
    simp only [factor, hv, if_false, map_mul, compAt_placeEmbed_self]
    refine Wloc_mul_of_isIntegral Pi w ?_ ?_ _
    · intro i j
      exact (k.val i j).2
    · rw [← map_inv]
      intro i j
      exact ((k⁻¹).val i j).2
  · exact factor_mul_placeEmbed S Pi v _ g hw

private theorem WfFun_mul_of_mem_levelOne (M : Ideal (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K M) : WfFun S Pi (g * u) = WfFun S Pi g := by
  rw [mem_levelOne_iff] at hu
  obtain ⟨h1, h2⟩ := hu
  unfold WfFun
  refine finprod_congr fun w => ?_
  unfold factor
  split_ifs with hS
  · rfl
  · rw [map_mul]
    refine Wloc_mul_of_isIntegral Pi w ?_ ?_ _
    · exact isIntegral_compAt_of_mem_integral fun i j => h1.integral i j w
    · refine isIntegral_compAt_inv_of_mem_integral fun i j => ?_
      rw [map_inv]
      exact h2.integral i j w

private theorem placeEmbed_mem_of_isIntegral (v : HeightOneSpectrum (𝓞 K)) {M : Ideal (𝓞 K)} (hM : ¬ v.asIdeal ∣ M)
    {k : GL (Fin 2) (v.adicCompletion K)} (hk : LocalWhittaker.IsIntegral Valued.v k)
    (hk' : LocalWhittaker.IsIntegral Valued.v k⁻¹) :
    placeEmbed K v k ∈ levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K := by
  have hMbot : M ≠ ⊥ := by
    rintro rfl
    exact hM (dvd_zero _)
  have hbound : idealBound (𝓞 K) M v = 1 := idealBound_eq_one_of_not_dvd hMbot hM
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v k) ∈ levelOne (𝓞 K) K M
    rw [finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
    refine ⟨⟨fun i j => hk i j, ?_, ?_⟩, ⟨fun i j => hk' i j, ?_, ?_⟩⟩
    · rw [hbound]; exact hk 1 0
    · rw [hbound]; exact (Valuation.map_sub _ _ _).trans (max_le (hk 1 1) (by simp))
    · rw [hbound]; exact hk' 1 0
    · rw [hbound]; exact (Valuation.map_sub _ _ _).trans (max_le (hk' 1 1) (by simp))
  · show finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v k) ∈ finiteAdelicGL2Subgroup K
    rw [mem_finiteAdelicGL2Subgroup_iff]
    exact glArch_finEmbed _ _ _

private theorem WfFun_eq_factor_mul_rest (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) :
    WfFun S Pi g = factor S Pi g v * ∏ᶠ w, Function.update (factor S Pi g) v 1 w :=
  finprod_eq_mul_finprod_update_one (mulSupport_factor_finite S Pi g) v

private theorem rest_mul_placeEmbed (v : HeightOneSpectrum (𝓞 K)) (h : GL (Fin 2) (v.adicCompletion K))
    (g : AdelicGL2 (𝓞 K) K) :
    Function.update (factor S Pi (g * placeEmbed K v h)) v 1 = Function.update (factor S Pi g) v 1 := by
  funext w
  by_cases hw : w = v
  · subst hw; simp
  · rw [Function.update_of_ne hw, Function.update_of_ne hw, factor_mul_placeEmbed S Pi v h g hw]

private theorem WfFun_mul_placeEmbed (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (h : GL (Fin 2) (v.adicCompletion K))
    (g : AdelicGL2 (𝓞 K) K) :
    WfFun S Pi (g * placeEmbed K v h)
      = Wloc Pi v (compAt v g * h) * ∏ᶠ w, Function.update (factor S Pi g) v 1 w := by
  rw [WfFun_eq_factor_mul_rest S Pi v, rest_mul_placeEmbed]
  simp only [factor, hv, if_false, map_mul, compAt_placeEmbed_self]

private theorem WfFun_eq_Wloc_mul_rest (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (g : AdelicGL2 (𝓞 K) K) :
    WfFun S Pi g = Wloc Pi v (compAt v g) * ∏ᶠ w, Function.update (factor S Pi g) v 1 w := by
  rw [WfFun_eq_factor_mul_rest S Pi v]
  simp only [factor, hv, if_false]

private theorem mapMatrix_scalar {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    f.mapMatrix (Matrix.scalar (Fin 2) a) = Matrix.scalar (Fin 2) (f a) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]

private theorem central_eq_placeEmbed_scalarPi (v : HeightOneSpectrum (𝓞 K)) :
    centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v))
      = placeEmbed K v (LocalWhittaker.scalarPi (unif K v) (unif_ne_zero K v)) := by
  set P := pd K v
  have hgen : heckeGen (𝓞 K) K v = placeEmbed K v (diagPi P.ϖ P.hϖ0) := P.hgen.symm
  rw [hgen]
  refine Units.ext ?_
  have hL : ((centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (placeEmbed K v (diagPi P.ϖ P.hϖ0)))
      : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      = Matrix.scalar (Fin 2) (Matrix.det (finMat (𝓞 K) K (localMat (𝓞 K) K v (diagPi P.ϖ P.hϖ0)))) := rfl
  have hR : ((placeEmbed K v (LocalWhittaker.scalarPi (unif K v) (unif_ne_zero K v)) : AdelicGL2 (𝓞 K) K)
      : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      = finMat (𝓞 K) K (localMat (𝓞 K) K v (LocalWhittaker.scalarPi (unif K v) (unif_ne_zero K v))) := rfl
  rw [hL, hR]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (R := 𝓞 K) (K := K) ?_ ?_
  · rw [mapMatrix_scalar, mapMatrix_arch_finMat, RingHom.map_det, mapMatrix_arch_finMat, Matrix.det_one,
      map_one]
  · rw [mapMatrix_scalar, mapMatrix_fin_finMat, RingHom.map_det, mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (R := 𝓞 K) (K := K) fun w => ?_
    rw [mapMatrix_scalar, RingHom.map_det]
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMat_self, mapMatrix_localMat_self, coe_diagPi, LocalWhittaker.coe_scalarPi,
        Matrix.det_fin_two_of]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, unif, P]
    · rw [mapMatrix_localMat_of_ne _ _ _ _ hw, mapMatrix_localMat_of_ne _ _ _ _ hw, Matrix.det_one,
        Matrix.scalar_apply, Matrix.diagonal_one]

private theorem WfFun_central_eigen
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (hb : Pi.b v ≠ 0) (g : AdelicGL2 (𝓞 K) K) :
    WfFun S Pi (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g)
      = Pi.toRawCentral.b v * WfFun S Pi g := by
  have hom : Pi.toRawCentral.b v ≠ 0 := by
    rw [HeckeEigensystem.toRawCentral_b]
    exact mul_ne_zero (inv_ne_zero (HeckeEigensystem.cNorm_ne_zero v)) hb
  rw [central_eq_placeEmbed_scalarPi]
  unfold WfFun
  rw [factor_placeEmbed_mul_eq_update S Pi v hv _ g (Pi.toRawCentral.b v)
    (localW_scalarPi_mul _ _ _ _ hom _ _ (valued_unif K v) _)]
  exact finprod_update_mul (mulSupport_factor_finite S Pi g) v _

private def ι (v : HeightOneSpectrum (𝓞 K)) (d : 𝓞 K) : v.adicCompletion K :=
  algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (algebraMap (𝓞 K) (v.adicCompletionIntegers K) d)

private theorem ι_eq (v : HeightOneSpectrum (𝓞 K)) (d : 𝓞 K) : ι v d = algebraMap (𝓞 K) (v.adicCompletion K) d := rfl

private theorem ι_add (v : HeightOneSpectrum (𝓞 K)) (d d' : 𝓞 K) : ι v (d + d') = ι v d + ι v d' := by
  simp only [ι_eq, map_add]

private theorem ι_sub (v : HeightOneSpectrum (𝓞 K)) (d d' : 𝓞 K) : ι v (d - d') = ι v d - ι v d' := by
  simp only [ι_eq, map_sub]

private theorem valued_ι_le_one (v : HeightOneSpectrum (𝓞 K)) (d : 𝓞 K) : Valued.v (ι v d) ≤ 1 :=
  (algebraMap (𝓞 K) (v.adicCompletionIntegers K) d).2

private theorem valued_ι_le_of_mem (v : HeightOneSpectrum (𝓞 K)) {d : 𝓞 K} (hd : d ∈ v.asIdeal) :
    Valued.v (ι v d) ≤ WithZero.exp (-1 : ℤ) := by
  have h1 : Valued.v (ι v d) = v.intValuation d := by
    rw [ι_eq]
    exact (valuedAdicCompletion_eq_valuation v d).trans (valuation_of_algebraMap v d)
  rw [h1]
  have h2 := (v.intValuation_le_pow_iff_dvd d 1).mpr (by rw [pow_one]; exact Ideal.dvd_span_singleton.mpr hd)
  simpa using h2

private theorem ι_injective (v : HeightOneSpectrum (𝓞 K)) : Function.Injective (ι v) := by
  intro d d' h
  simp only [ι_eq] at h
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K),
    IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) d'] at h
  exact IsFractionRing.injective (𝓞 K) K ((algebraMap K (v.adicCompletion K)).injective h)

private theorem valued_unif_zpow (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    Valued.v (unif K v ^ n) = WithZero.exp (-n) := by
  rw [map_zpow₀, valued_unif, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem psi_unif_mul_eq_one (v : HeightOneSpectrum (𝓞 K)) {t : v.adicCompletion K}
    (ht : Valued.v t ≤ WithZero.exp (-1 : ℤ)) :
    StandardAddChar.psiLocal K v (unif K v ^ (-lvl K v - 1) * t) = 1 := by
  refine (level_law v).1 _ ?_
  rw [map_mul, valued_unif_zpow]
  calc WithZero.exp (-(-lvl K v - 1)) * Valued.v t
      ≤ WithZero.exp (-(-lvl K v - 1)) * WithZero.exp (-1 : ℤ) := mul_le_mul_right ht _
    _ = WithZero.exp (lvl K v) := by rw [← WithZero.exp_add]; congr 1; ring

private def resChar (v : HeightOneSpectrum (𝓞 K)) (q : 𝓞 K ⧸ v.asIdeal) : ℂ :=
  StandardAddChar.psiLocal K v (unif K v ^ (-lvl K v - 1) * ι v ((pd K v).sec q))

private theorem resChar_mul (v : HeightOneSpectrum (𝓞 K)) (q q' : 𝓞 K ⧸ v.asIdeal) :
    resChar v (q + q') = resChar v q * resChar v q' := by
  set P := pd K v
  have hd : P.sec (q + q') - P.sec q - P.sec q' ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, P.hsec, P.hsec, P.hsec, add_sub_cancel_left, sub_self]
  have hsplit : P.sec (q + q') = P.sec q + P.sec q' + (P.sec (q + q') - P.sec q - P.sec q') := by ring
  unfold resChar
  rw [hsplit, ι_add, ι_add, mul_add, mul_add, psi_add, psi_add, psi_unif_mul_eq_one v (valued_ι_le_of_mem v hd),
    mul_one]

private theorem exists_resChar_ne_one (v : HeightOneSpectrum (𝓞 K)) : ∃ q : 𝓞 K ⧸ v.asIdeal, resChar v q ≠ 1 := by
  set P := pd K v
  obtain ⟨x, hxv, hx1⟩ := (level_law v).2
  obtain ⟨y, hy⟩ : ∃ y : v.adicCompletion K, y = unif K v ^ (lvl K v + 1) * x := ⟨_, rfl⟩
  have hyint : y ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, hy, map_mul, valued_unif_zpow]
    calc WithZero.exp (-(lvl K v + 1)) * Valued.v x
        ≤ WithZero.exp (-(lvl K v + 1)) * WithZero.exp (lvl K v + 1) := mul_le_mul_right hxv _
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  obtain ⟨z, hz⟩ := exists_global_sub_mem_of_approx (R := 𝓞 K) (K := K) v
    (fun a => IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_adicCompletionIntegers K a)
    (fun t => StandardAddChar.finAdeleSingleAt K v t)
    (fun t => StandardAddChar.finAdeleSingleAt_apply_self K v t)
    (fun t w hw => StandardAddChar.finAdeleSingleAt_apply_of_ne K v t hw) y hyint
  refine ⟨Ideal.Quotient.mk v.asIdeal z, ?_⟩
  have hsz : P.sec (Ideal.Quotient.mk v.asIdeal z) - z ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, P.hsec, sub_self]
  have hπ : unif K v ^ (-lvl K v - 1) * unif K v ^ (lvl K v + 1) = 1 := by
    rw [← zpow_add₀ (unif_ne_zero K v)]
    simp
  have hx : unif K v ^ (-lvl K v - 1) * y = x := by
    rw [hy, ← mul_assoc, hπ, one_mul]
  have hdecomp : unif K v ^ (-lvl K v - 1) * ι v (P.sec (Ideal.Quotient.mk v.asIdeal z))
      = x + (unif K v ^ (-lvl K v - 1) * ι v (P.sec (Ideal.Quotient.mk v.asIdeal z) - z)
          + unif K v ^ (-lvl K v - 1) * (ι v z - y)) := by
    rw [ι_sub]
    linear_combination hx
  unfold resChar
  rw [hdecomp, psi_add, psi_add, psi_unif_mul_eq_one v (valued_ι_le_of_mem v hsz)]
  have hzy : Valued.v (ι v z - y) ≤ WithZero.exp (-1 : ℤ) := by
    rw [← Valuation.map_neg, neg_sub]
    exact hz
  rw [psi_unif_mul_eq_one v hzy, mul_one, mul_one]
  exact hx1

private theorem sum_resChar (v : HeightOneSpectrum (𝓞 K)) : ∑ q : 𝓞 K ⧸ v.asIdeal, resChar v q = 0 :=
  sum_eq_zero_of_mul_of_ne_one (resChar v) (resChar_mul v) (exists_resChar_ne_one v)

private def rloc (v : HeightOneSpectrum (𝓞 K)) (o : Option (𝓞 K ⧸ v.asIdeal)) : GL (Fin 2) (v.adicCompletion K) :=
  o.elim (localRepInf (pd K v).ϖ (pd K v).hϖ0)
    (fun c => localRepSome (pd K v).ϖ (pd K v).hϖ0 (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ((pd K v).sec c)))

private theorem rloc_none (v : HeightOneSpectrum (𝓞 K)) :
    rloc v none = LocalWhittaker.repInf (unif K v) (unif_ne_zero K v) := by
  refine Units.ext ?_
  show ((localRepInf (pd K v).ϖ (pd K v).hϖ0 : GL (Fin 2) (v.adicCompletion K))
      : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = _
  exact (coe_localRepInf ..).trans rfl

private theorem rloc_some (v : HeightOneSpectrum (𝓞 K)) (c : 𝓞 K ⧸ v.asIdeal) :
    rloc v (some c) = LocalWhittaker.repSome (unif K v) (unif_ne_zero K v) (ι v ((pd K v).sec c)) := by
  refine Units.ext ?_
  show ((localRepSome (pd K v).ϖ (pd K v).hϖ0 _ : GL (Fin 2) (v.adicCompletion K))
      : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = _
  exact (coe_localRepSome ..).trans rfl

private theorem hsys_rloc (v : HeightOneSpectrum (𝓞 K)) (M : Ideal (𝓞 K)) (hM : ¬ v.asIdeal ∣ M) :
    HeckeIntegralSeam.IsHeckeCosetSystem (levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v)
      (fun o => placeEmbed K v (rloc v o)) :=
  (pd K v).hsys M hM

private theorem card_residue (v : HeightOneSpectrum (𝓞 K)) :
    Fintype.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

private def resSet (v : HeightOneSpectrum (𝓞 K)) : Finset (v.adicCompletion K) :=
  Finset.univ.image fun c : 𝓞 K ⧸ v.asIdeal => ι v ((pd K v).sec c)

private theorem sec_injective (v : HeightOneSpectrum (𝓞 K)) : Function.Injective (pd K v).sec := by
  intro c c' h
  rw [← (pd K v).hsec c, ← (pd K v).hsec c', h]

private theorem resParam_injective (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective fun c : 𝓞 K ⧸ v.asIdeal => ι v ((pd K v).sec c) :=
  (ι_injective v).comp (sec_injective v)

private theorem sum_resSet (v : HeightOneSpectrum (𝓞 K)) (f : v.adicCompletion K → ℂ) :
    ∑ β ∈ resSet v, f β = ∑ c : 𝓞 K ⧸ v.asIdeal, f (ι v ((pd K v).sec c)) := by
  unfold resSet
  rw [Finset.sum_image fun c _ c' _ h => resParam_injective v h]

private theorem card_resSet (v : HeightOneSpectrum (𝓞 K)) : ((resSet v).card : ℂ) = HeckeEigensystem.cNorm v := by
  unfold resSet
  rw [Finset.card_image_of_injective _ (resParam_injective v), Finset.card_univ, card_residue, HeckeEigensystem.cNorm]

private theorem torusElt_eq (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) (m n : ℤ) :
    LocalWhittaker.unipotent x * LocalWhittaker.diagZ (unif K v) (unif_ne_zero K v) m
        * LocalWhittaker.scalarPi (unif K v) (unif_ne_zero K v) ^ n
      = LocalWhittaker.torusElt (unif K v) (unif_ne_zero K v) x m n := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, LocalWhittaker.coe_scalarPi_zpow, LocalWhittaker.coe_unipotent,
    LocalWhittaker.coe_diagZ, LocalWhittaker.coe_torusElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem local_hecke (Pi : HeckeEigensystem K ℂ) (v : HeightOneSpectrum (𝓞 K)) (hb : Pi.b v ≠ 0)
    (x : v.adicCompletion K) (m n : ℤ) :
    ∑ o : Option (𝓞 K ⧸ v.asIdeal),
        Wloc Pi v (LocalWhittaker.torusElt (unif K v) (unif_ne_zero K v) x m n * rloc v o)
      = Pi.a v * Wloc Pi v (LocalWhittaker.torusElt (unif K v) (unif_ne_zero K v) x m n) := by
  have hom : Pi.toRawCentral.b v ≠ 0 := by
    rw [HeckeEigensystem.toRawCentral_b]
    exact mul_ne_zero (inv_ne_zero (HeckeEigensystem.cNorm_ne_zero v)) hb
  have hL3 := hecke_identity_torusElt Valued.v (StandardAddChar.psiLocal K v) (cseq Pi v) (Pi.toRawCentral.b v)
    (unif K v) (unif_ne_zero K v) (valued_unif K v) hom (lvl K v) (HeckeEigensystem.cNorm v) (Pi.a v) (resSet v)
    (psi_add v)
    (level_law v).1
    (by
      intro β hβ
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hβ
      exact valued_ι_le_one v _)
    (card_resSet v)
    (by
      rw [sum_resSet]
      exact sum_resChar v)
    (fun k hk => cseq_eq_zero Pi v hk)
    (fun k hk => torusFactor_shift_rec (HeckeEigensystem.cNorm v) (Pi.a v) (Pi.toRawCentral.b v)
      (HeckeEigensystem.cNorm_ne_zero v) (lvl K v) k hk)
    x m n
  rw [Fintype.sum_option, add_comm, rloc_none]
  simp only [rloc_some]
  rw [← sum_resSet v (fun β => Wloc Pi v (LocalWhittaker.torusElt (unif K v) (unif_ne_zero K v) x m n
    * LocalWhittaker.repSome (unif K v) (unif_ne_zero K v) β))]
  exact hL3

private theorem WfFun_hecke_eigen (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (hb : Pi.b v ≠ 0) (M : Ideal (𝓞 K))
    (hM : ¬ v.asIdeal ∣ M) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
      (heckeGen (𝓞 K) K v) v (WfFun S Pi) (Pi.a v) := by
  classical
  set U := levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K with hU
  let e : Fin (Ideal.absNorm v.asIdeal + 1) ≃ Option (𝓞 K ⧸ v.asIdeal) :=
    (finSuccEquiv _).trans (Equiv.optionCongr (Fintype.equivFinOfCardEq (card_residue v)).symm)
  have hsys := isHeckeCosetSystem_comp_equiv (hsys_rloc v M hM) e
  refine ⟨fun i => placeEmbed K v (rloc v (e i)), hsys, fun g => ?_⟩
  obtain ⟨x, m, n, k, hk⟩ :=
    exists_iwasawa (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (unif K v) (unif_ne_zero K v)
      (valued_unif K v) (compAt v g)
  set kK := Matrix.GeneralLinearGroup.map (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).integer.subtype k
    with hkK
  have hkint : LocalWhittaker.IsIntegral Valued.v kK := isIntegral_map _ k
  have hkint' : LocalWhittaker.IsIntegral Valued.v kK⁻¹ := by
    rw [hkK, ← map_inv]
    exact isIntegral_map _ k⁻¹
  set u := placeEmbed K v kK with hu_def
  have hu : u ∈ U := placeEmbed_mem_of_isIntegral v hM hkint hkint'
  have huM : u ∈ levelOne (𝓞 K) K M := (Subgroup.mem_inf.mp hu).1
  set g' := g * u⁻¹ with hg'
  have hg : g = g' * u := by rw [hg', inv_mul_cancel_right]
  have hinv : ∀ h : AdelicGL2 (𝓞 K) K, ∀ w ∈ U, WfFun S Pi (h * w) = WfFun S Pi h :=
    fun h w hw => WfFun_mul_of_mem_levelOne S Pi M h (Subgroup.mem_inf.mp hw).1
  have h1 : SmoothCusp.heckeCosetSum K (fun i => placeEmbed K v (rloc v (e i))) (WfFun S Pi) g
      = ∑ i, WfFun S Pi (g' * placeEmbed K v (rloc v (e i))) := by
    have := HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys (isHeckeCosetSystem_mul_left hsys hu)
      hinv g'
    unfold SmoothCusp.heckeCosetSum
    rw [hg]
    simpa only [mul_assoc] using this
  have h2 : WfFun S Pi g = WfFun S Pi g' := by
    conv_lhs => rw [hg]
    exact WfFun_mul_of_mem_levelOne S Pi M g' huM
  rw [h1, h2]
  have hcomp : compAt v g' = LocalWhittaker.torusElt (unif K v) (unif_ne_zero K v) x m n := by
    rw [hg', map_mul, map_inv, hu_def, compAt_placeEmbed_self, hk, mul_inv_cancel_right, torusElt_eq]
  rw [Fintype.sum_equiv e (fun i => WfFun S Pi (g' * placeEmbed K v (rloc v (e i))))
    (fun o => WfFun S Pi (g' * placeEmbed K v (rloc v o))) (fun _ => rfl)]
  simp only [WfFun_mul_placeEmbed S Pi v hv, hcomp]
  rw [← Finset.sum_mul, local_hecke Pi v hb x m n, WfFun_eq_Wloc_mul_rest S Pi v hv g', hcomp, mul_assoc]

end Fields

private theorem isIntegral_one (v : HeightOneSpectrum (𝓞 K)) :
    LocalWhittaker.IsIntegral (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) 1 := by
  intro i j
  rw [Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

private theorem exists_components (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ g : AdelicGL2 (𝓞 K) K,
      (∀ w ∈ T, compAt w g = LocalWhittaker.diagZ (unif K w) (unif_ne_zero K w) (-lvl K w)) ∧
        ∀ w ∉ T, compAt w g = 1 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1, fun w hw => absurd hw (Finset.notMem_empty w), fun w _ => map_one _⟩
  | insert w₀ T hw₀ ih =>
    obtain ⟨g, hgT, hgout⟩ := ih
    refine ⟨g * placeEmbed K w₀ (LocalWhittaker.diagZ (unif K w₀) (unif_ne_zero K w₀) (-lvl K w₀)), ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hwT
      · rw [map_mul, compAt_placeEmbed_self, hgout w hw₀, one_mul]
      · have hne : w ≠ w₀ := fun h => hw₀ (h ▸ hwT)
        rw [map_mul, compAt_placeEmbed_of_ne hne, mul_one, hgT w hwT]
    · intro w hw
      have hne : w ≠ w₀ := fun h => hw (h ▸ Finset.mem_insert_self _ _)
      have hwT : w ∉ T := fun h => hw (Finset.mem_insert_of_mem h)
      rw [map_mul, compAt_placeEmbed_of_ne hne, mul_one, hgout w hwT]

private theorem exists_WfFun_ne_zero (S : Finset (HeightOneSpectrum (𝓞 K))) (Pi : HeckeEigensystem K ℂ) :
    ∃ g, WfFun S Pi g ≠ 0 := by
  have hL := eventually_level_eq_zero (R := 𝓞 K) (K := K)
    (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) (lvl K)
    (fun w => LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal K w)
  have hfin : {w : HeightOneSpectrum (𝓞 K) | lvl K w ≠ 0}.Finite := Filter.eventually_cofinite.mp hL
  obtain ⟨g, hgT, hgout⟩ := exists_components (K := K) hfin.toFinset
  refine ⟨g, ?_⟩
  have hone : WfFun S Pi g = 1 := by
    unfold WfFun
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    unfold factor
    split_ifs with hS
    · rfl
    · by_cases hw : lvl K w = 0
      · have hwT : w ∉ hfin.toFinset := by simpa using hw
        rw [hgout w hwT]
        exact Wloc_one_of_isIntegral_of_lvl Pi w (isIntegral_one w) (by rw [inv_one]; exact isIntegral_one w) hw
      · have hwT : w ∈ hfin.toFinset := by simpa using hw
        rw [hgT w hwT, Wloc_diagZ, cseq_neg_lvl]
  rw [hone]
  exact one_ne_zero

end FiniteWhittaker
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_finWhittakerDatum_Wf_ne_zero.FiniteWhittaker"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_finWhittakerDatum_Wf_ne_zero.FiniteWhittaker"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_finWhittakerDatum_Wf_ne_zero.FiniteWhittaker"

open IsDedekindDomain NumberField AutomorphicForm in
open LanglandsTunnell in
open LanglandsTunnell.Converse in

theorem solution (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Pi : HeckeEigensystem K ℂ) (hb : ∀ v ∉ S, Pi.b v ≠ 0) :
    ∃ D : FinWhittakerDatum K S Pi, ∃ g, D.Wf g ≠ 0 := by
  obtain ⟨g, hg⟩ := FiniteWhittaker.exists_WfFun_ne_zero S Pi
  exact ⟨{ Wf := FiniteWhittaker.WfFun S Pi,
            finite_dependent := FiniteWhittaker.WfFun_finite_dependent S Pi,
            blind_at := fun v hv h g => FiniteWhittaker.WfFun_blind_at S Pi v hv h g,
            unipotent_left := fun v hv x g => FiniteWhittaker.WfFun_unipotent_left S Pi v hv x g,
            integral_right := fun v hv k g => FiniteWhittaker.WfFun_integral_right S Pi v hv k g,
            hecke_eigen := fun v hv M hM => FiniteWhittaker.WfFun_hecke_eigen S Pi v hv (hb v hv) M hM,
            central_eigen := fun v hv g => FiniteWhittaker.WfFun_central_eigen S Pi v hv (hb v hv) g,
            level_right := ⟨⊤, top_ne_bot,
              fun g u hu => FiniteWhittaker.WfFun_mul_of_mem_levelOne S Pi ⊤ g (Subgroup.mem_inf.mp hu).1⟩ }, g, hg⟩

end S_LanglandsTunnell_Converse_exists_finWhittakerDatum_Wf_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_finWhittakerDatum_Wf_ne_zero (solution)
