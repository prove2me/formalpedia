-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.coefficientFn_eq_sum_jacquetWhittaker3_of_isWhittakerFunctional3_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b3a98a8c-332e-5d32-8fda-6a59375fa299

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_smul_of_isWhittakerFunctional3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_coefficientFn_eq_sum_jacquetWhittaker3_of_isWhittakerFunctional3_inv
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

p2m_open "MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_coefficientFn_eq_sum_jacquetWhittaker3_of_isWhittakerFunctional3_inv.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel TateLocal.psiLocal_ne_one CubicInduction.exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum CubicInduction.exists_eq_smul_of_isWhittakerFunctional3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono jacquetHaar3 jacquetTruncated3 jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue cellSectionOf jacquetWhittaker3 diagonal3 principalSeries3 rightTranslate_mem_principalSeries3 coefficientFn IsWhittakerFunctional3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det cellRatio cellCutoff cellValue cellSection antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 gl3Det_antidiagonal3 antidiagonal3_mem_cellCutoff cellSection_antidiagonal3_ne_zero isClopen_valued_le_one cellSection_mem_principalSeries3 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe LocalGL3 properSpace_adicCompletion_rat exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum exists_eq_smul_of_isWhittakerFunctional3"
namespace T0SolAux
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"
section Entries

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl3Entry_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 2 0 = 1 ∧
      gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 2 1 = x ∧
      gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 2 2 = z ∧
      gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 1 0 = 0 ∧
      gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 1 1 = 1 ∧
      gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 1 2 = y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [gl3Entry, Units.val_mul, antidiagonal3_coe, upperUnipotent3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem cornerEntry_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    cornerEntry v (antidiagonal3 v * upperUnipotent3 x y z) = 1 :=
  (gl3Entry_antidiagonal3_mul_upperUnipotent3 v x y z).1

private theorem lowerMinor_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    lowerMinor v (antidiagonal3 v * upperUnipotent3 x y z) = -1 := by
  obtain ⟨h20, h21, -, h10, h11, -⟩ := gl3Entry_antidiagonal3_mul_upperUnipotent3 v x y z
  simp [lowerMinor, h20, h21, h10, h11]

private theorem outerMinor_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    outerMinor v (antidiagonal3 v * upperUnipotent3 x y z) = -y := by
  obtain ⟨h20, -, h22, h10, -, h12⟩ := gl3Entry_antidiagonal3_mul_upperUnipotent3 v x y z
  simp [outerMinor, h20, h22, h10, h12]

private theorem gl3Det_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    gl3Det v (antidiagonal3 v * upperUnipotent3 x y z) = -1 := by
  simp [gl3Det, Units.val_mul, Matrix.det_mul, antidiagonal3_coe, upperUnipotent3_coe, Matrix.det_fin_three]

private theorem cellRatio_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    cellRatio v (antidiagonal3 v * upperUnipotent3 x y z) = ![x, z, y] := by
  obtain ⟨h20, h21, h22, -, -, -⟩ := gl3Entry_antidiagonal3_mul_upperUnipotent3 v x y z
  have hc := cornerEntry_antidiagonal3_mul_upperUnipotent3 v x y z
  have hl := lowerMinor_antidiagonal3_mul_upperUnipotent3 v x y z
  have ho := outerMinor_antidiagonal3_mul_upperUnipotent3 v x y z
  ext i
  fin_cases i <;> simp [cellRatio, hc, hl, ho, h21, h22, neg_div_neg_eq]

private theorem antidiagonal3_mul_upperUnipotent3_mem_cellCutoff_iff
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 ∈ cellCutoff v ↔ p ∈ unipotentBall3 v 0 := by
  rw [mem_unipotentBall3_iff]
  simp only [cellCutoff, Set.mem_setOf_eq, cornerEntry_antidiagonal3_mul_upperUnipotent3,
    lowerMinor_antidiagonal3_mul_upperUnipotent3, cellRatio_antidiagonal3_mul_upperUnipotent3, ne_eq,
    one_ne_zero, not_false_eq_true, neg_eq_zero, true_and, Fin.forall_fin_succ, IsEmpty.forall_iff, and_true,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_succ, WithZero.exp_zero, mul_zero]
  tauto

private theorem cellValue_antidiagonal3_mul_upperUnipotent3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (x y z : v.adicCompletion ℚ) :
    cellValue v χ (antidiagonal3 v * upperUnipotent3 x y z) = cellValue v χ (antidiagonal3 v) := by
  simp only [cellValue, gl3Det_antidiagonal3_mul_upperUnipotent3, lowerMinor_antidiagonal3_mul_upperUnipotent3,
    cornerEntry_antidiagonal3_mul_upperUnipotent3, gl3Det_antidiagonal3, lowerMinor_antidiagonal3,
    cornerEntry_antidiagonal3]

private theorem cellSection_antidiagonal3_mul_upperUnipotent3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    cellSection v χ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2) =
      (unipotentBall3 v 0).indicator (fun _ => cellValue v χ (antidiagonal3 v)) p := by
  by_cases hp : p ∈ unipotentBall3 v 0
  · rw [Set.indicator_of_mem hp, cellSection,
      Set.indicator_of_mem ((antidiagonal3_mul_upperUnipotent3_mem_cellCutoff_iff v p).mpr hp),
      cellValue_antidiagonal3_mul_upperUnipotent3]
  · rw [Set.indicator_of_notMem hp, cellSection,
      Set.indicator_of_notMem (fun h => hp ((antidiagonal3_mul_upperUnipotent3_mem_cellCutoff_iff v p).mp h))]

private theorem psiLocal_neg_add_eq_one_of_mem_unipotentBall3_zero
    (p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) (hp : p ∈ unipotentBall3 v 0) :
    psiLocal ℚ v (-(p.1 + p.2.1)) = 1 := by
  rw [mem_unipotentBall3_iff, WithZero.exp_zero] at hp
  apply LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_neg]
  exact (Valuation.map_add_le_max' _ _ _).trans (max_le hp.1 hp.2.1)

private theorem unipotentBall3_zero_eq_prod :
    unipotentBall3 v 0 = {x : v.adicCompletion ℚ | Valued.v x ≤ 1} ×ˢ
      ({x : v.adicCompletion ℚ | Valued.v x ≤ 1} ×ˢ {x : v.adicCompletion ℚ | Valued.v x ≤ 1}) := by
  ext p
  simp [mem_unipotentBall3_iff, WithZero.exp_zero]

private theorem setOf_valued_le_one_eq_integers :
    {x : v.adicCompletion ℚ | Valued.v x ≤ 1} = (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  ext x
  simp [HeightOneSpectrum.mem_adicCompletionIntegers]

end Entries

private theorem jacquetTruncated3_cellSection_of_nonneg (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (c : ℤ) (hc : 0 ≤ c) :
    jacquetTruncated3 v c (cellSection v χ) =
      (letI := localBorel ℚ v; (jacquetHaar3 v (unipotentBall3 v 0)).toReal) * cellValue v χ (antidiagonal3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  have hS : MeasurableSet {x : v.adicCompletion ℚ | Valued.v x ≤ 1} :=
    (isClopen_valued_le_one v).isClosed.measurableSet
  have hmeas : MeasurableSet (unipotentBall3 v 0) := by
    rw [unipotentBall3_zero_eq_prod]
    exact hS.prod (hS.prod hS)
  have hF : (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      psiLocal ℚ v (-(p.1 + p.2.1)) * cellSection v χ (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)) =
      (unipotentBall3 v 0).indicator (fun _ => cellValue v χ (antidiagonal3 v)) := by
    funext p
    by_cases hp : p ∈ unipotentBall3 v 0
    · rw [cellSection_antidiagonal3_mul_upperUnipotent3, Set.indicator_of_mem hp,
        psiLocal_neg_add_eq_one_of_mem_unipotentBall3_zero v p hp, one_mul]
    · rw [cellSection_antidiagonal3_mul_upperUnipotent3, Set.indicator_of_notMem hp, mul_zero]
  simp only [jacquetTruncated3]
  rw [hF, setIntegral_indicator hmeas, Set.inter_eq_right.mpr (unipotentBall3_mono v hc), setIntegral_const,
    measureReal_def, Complex.real_smul]

private theorem jacquetValue_cellSection_ne_zero (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : jacquetValue v (cellSection v χ) ≠ 0 := by
  letI := localBorel ℚ v
  have hC : cellValue v χ (antidiagonal3 v) ≠ 0 := by
    have h := cellSection_antidiagonal3_ne_zero v χ
    rwa [cellSection, Set.indicator_of_mem (antidiagonal3_mem_cellCutoff v)] at h
  have hvol : (selfDualHaarAt ℚ v).real {x : v.adicCompletion ℚ | Valued.v x ≤ 1} ≠ 0 := by
    rw [setOf_valued_le_one_eq_integers]
    intro h0
    have h := LanglandsTunnell.TateLocal.selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel ℚ v
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  have hball : (jacquetHaar3 v (unipotentBall3 v 0)).toReal ≠ 0 := by
    haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
    haveI : ProperSpace (v.adicCompletion ℚ) := properSpace_adicCompletion_rat v
    haveI hH : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
      unfold selfDualHaarAt
      refine Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos ?_).ne'
      exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot))
    haveI : SigmaFinite (selfDualHaarAt ℚ v) := inferInstance
    rw [unipotentBall3_zero_eq_prod]
    simp only [jacquetHaar3, Measure.prod_prod, ENNReal.toReal_mul]
    rw [measureReal_def] at hvol
    exact mul_ne_zero hvol (mul_ne_zero hvol hvol)
  have hconst : ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      jacquetTruncated3 v c (cellSection v χ) = jacquetTruncated3 v c₀ (cellSection v χ) :=
    ⟨0, fun c hc => by
      rw [jacquetTruncated3_cellSection_of_nonneg v χ c (by exact_mod_cast hc),
        jacquetTruncated3_cellSection_of_nonneg v χ ((0 : ℕ) : ℤ) (by simp)]⟩
  have h1 := jacquetTruncated3_eq_jacquetValue v (cellSection v χ) hconst
    (c := max (jacquetLevel v (cellSection v χ) : ℤ) 0) (le_max_left _ _)
  rw [← h1, jacquetTruncated3_cellSection_of_nonneg v χ _ (le_max_right _ _)]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hball) hC

private theorem gl3AmbientRightTranslate_gl3AmbientRightTranslate (v : HeightOneSpectrum (𝓞 ℚ))
    (g h : LocalGL3 v) (W : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) h (gl3AmbientRightTranslate (R := ℂ) g W) =
      gl3AmbientRightTranslate (R := ℂ) (h * g) W := by
  funext x
  simp [gl3AmbientRightTranslate_apply, mul_assoc]

private theorem gl3AmbientRightTranslate_one' (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) (1 : LocalGL3 v) W = W := by
  funext x
  simp [gl3AmbientRightTranslate_apply]

end LanglandsTunnell.CubicInduction.T0SolAux

open LanglandsTunnell.CubicInduction.T0SolAux

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)
    (hΛ : IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ Λ)
    (f : ↥(principalSeries3 v χ)) :
    ∃ (n : ℕ) (κ : Fin n → ℂ) (x y z : Fin n → v.adicCompletion ℚ) (Φ : Fin n → (Fin 3 → v.adicCompletion ℚ) → ℂ),
      (∀ j, IsLocallyConstant (Φ j) ∧ HasCompactSupport (Φ j)) ∧
      coefficientFn Λ f = fun h =>
        ∑ j, κ j * jacquetWhittaker3 v χ (Φ j)
          (diagonal3 v ![1, -1, 1] * h * (upperUnipotent3 (x j) (y j) (z j) * antidiagonal3 v)) := by
  obtain ⟨Λ₀, Λ₁, -, hval, -, hdec, hΛ₁, hval₁, hcoef₁⟩ :=
    LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum v χ hχ

  have hΛ₁Λ₀ : ∀ F : ↥(principalSeries3 v χ), Λ₁ F =
      Λ₀ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, -1, 1]) F,
        rightTranslate_mem_principalSeries3 F.2 (diagonal3 v ![1, -1, 1])⟩ := by
    intro F
    rw [hval₁ F, hval]

  have hne : Λ₁ ≠ 0 := by
    intro h0
    have hcs : cellSection v χ ∈ principalSeries3 v χ := cellSection_mem_principalSeries3 v χ hχ
    have hF : (⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, -1, 1])
          (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, -1, 1])⁻¹ (cellSection v χ)),
        rightTranslate_mem_principalSeries3
          (rightTranslate_mem_principalSeries3 hcs (diagonal3 v ![1, -1, 1])⁻¹) (diagonal3 v ![1, -1, 1])⟩ :
          ↥(principalSeries3 v χ)) = ⟨cellSection v χ, hcs⟩ := by
      apply Subtype.ext
      simp only [gl3AmbientRightTranslate_gl3AmbientRightTranslate, mul_inv_cancel,
        gl3AmbientRightTranslate_one']
    have h1 := hΛ₁Λ₀ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, -1, 1])⁻¹ (cellSection v χ),
      rightTranslate_mem_principalSeries3 hcs (diagonal3 v ![1, -1, 1])⁻¹⟩
    rw [h0, LinearMap.zero_apply, hF, hval] at h1
    exact jacquetValue_cellSection_ne_zero v χ h1.symm
  have hψ : (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ ≠ 1 := by
    rw [ne_eq, inv_eq_one]
    exact LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v
  obtain ⟨c, hc⟩ :=
    LanglandsTunnell.CubicInduction.exists_eq_smul_of_isWhittakerFunctional3 v χ _ hψ Λ₁ Λ hΛ₁ hne hΛ
  obtain ⟨n, κ, x, y, z, Φ, hΦ, hf⟩ := hdec f
  choose hm hg using fun j => hcoef₁ (Φ j) (hΦ j)
  refine ⟨n, fun j => c * κ j, x, y, z, Φ, hΦ, ?_⟩
  funext h
  have hmem : ∀ j, gl3AmbientRightTranslate (R := ℂ) (h * (upperUnipotent3 (x j) (y j) (z j) * antidiagonal3 v))
      (cellSectionOf v χ (Φ j)) ∈ principalSeries3 v χ :=
    fun j => rightTranslate_mem_principalSeries3 (hm j) _

  have hmember : (⟨gl3AmbientRightTranslate (R := ℂ) h f, rightTranslate_mem_principalSeries3 f.2 h⟩ :
      ↥(principalSeries3 v χ)) = ∑ j, κ j • (⟨_, hmem j⟩ : ↥(principalSeries3 v χ)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [hf]
    simp only [map_sum, map_smul, gl3AmbientRightTranslate_gl3AmbientRightTranslate]
  calc coefficientFn Λ f h
      = Λ ⟨gl3AmbientRightTranslate (R := ℂ) h f, rightTranslate_mem_principalSeries3 f.2 h⟩ := rfl
    _ = c * Λ₁ ⟨gl3AmbientRightTranslate (R := ℂ) h f, rightTranslate_mem_principalSeries3 f.2 h⟩ := by
        rw [hc]
        rfl
    _ = c * ∑ j, κ j * Λ₁ ⟨_, hmem j⟩ := by
        rw [hmember, map_sum]
        simp only [map_smul, smul_eq_mul]
    _ = ∑ j, (c * κ j) * jacquetWhittaker3 v χ (Φ j)
          (diagonal3 v ![1, -1, 1] * h * (upperUnipotent3 (x j) (y j) (z j) * antidiagonal3 v)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hgj := congrFun (hg j) (h * (upperUnipotent3 (x j) (y j) (z j) * antidiagonal3 v))
        rw [mul_assoc (diagonal3 v ![1, -1, 1]) h, hgj, mul_assoc]
        rfl

end S_LanglandsTunnell_CubicInduction_coefficientFn_eq_sum_jacquetWhittaker3_of_isWhittakerFunctional3_inv
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_coefficientFn_eq_sum_jacquetWhittaker3_of_isWhittakerFunctional3_inv (solution)
