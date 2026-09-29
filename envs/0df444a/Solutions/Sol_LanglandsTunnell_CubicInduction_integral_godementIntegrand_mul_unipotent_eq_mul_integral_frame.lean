-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b1296c47-04be-5bd1-a87b-50780ed4d64c

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Theorems.Thm_NumberField_AdicCompletion_map_matrix_mulVec_pi_eq_smul_pi
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction NumberField.StandardAddChar

open scoped ENNReal NNReal

noncomputable section

namespace GodFibre

section LocalField

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

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

theorem levelBall_mem_nhds (n : ℤ) : {y : F | Valued.v y ≤ WithZero.exp n} ∈ nhds (0 : F) := by
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer ℚ p
  set πF : F := (((WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation ℚ p)).symm π :
      WithVal (IsDedekindDomain.HeightOneSpectrum.valuation ℚ p)) : F) with hπF
  have hvπ : Valued.v πF = WithZero.exp (-1 : ℤ) := by
    rw [hπF, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hπ0 : πF ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hvπ; exact WithZero.zero_ne_coe hvπ
  set c : F := πF ^ (-n) with hc
  have hvc : Valued.v c = WithZero.exp n := by
    rw [hc, map_zpow₀, hvπ, ← WithZero.exp_zsmul]; congr 1; ring
  have hc0 : c ≠ 0 := by rw [hc]; exact zpow_ne_zero _ hπ0
  have hset : {y : F | Valued.v y ≤ WithZero.exp n} = Metric.closedBall (0 : F) ‖c‖ := by
    ext y
    rw [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right, ← hvc, Valued.toNormedField.norm_le_iff]
  rw [hset]
  exact (IsUltrametricDist.isOpen_closedBall (0 : F) (norm_ne_zero_iff.2 hc0)).mem_nhds
    (Metric.mem_closedBall_self (norm_nonneg _))

theorem isLocallyConstant_of_level (θ : AddChar F ℂ) (n : ℤ)
    (hθn : ∀ x : F, Valued.v x ≤ WithZero.exp n → θ x = 1) :
    IsLocallyConstant (fun t : F => (θ t : ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hnhds : {y : F | Valued.v (y - x) ≤ WithZero.exp n} ∈ nhds x := by
    have h := levelBall_mem_nhds p n
    have : (fun y : F => y - x) ⁻¹' {z : F | Valued.v z ≤ WithZero.exp n} = {y : F | Valued.v (y - x) ≤ WithZero.exp n} := rfl
    rw [← this]
    exact (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using h)
  filter_upwards [hnhds] with y hy
  have h1 : θ (y - x) = 1 := hθn (y - x) hy
  have : y = (y - x) + x := by ring
  rw [this, AddChar.map_add_eq_mul, h1, one_mul]

theorem continuous_of_level (θ : AddChar F ℂ) (n : ℤ)
    (hθn : ∀ x : F, Valued.v x ≤ WithZero.exp n → θ x = 1) : Continuous (fun t : F => (θ t : ℂ)) :=
  (isLocallyConstant_of_level p θ n hθn).continuous

end LocalField

section ChangeOfVariables

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

def vec2 (q : F × F) : Fin 2 → F := ![q.1, q.2]

@[scoped simp] theorem vec2_zero (q : F × F) : vec2 p q 0 = q.1 := rfl
@[scoped simp] theorem vec2_one (q : F × F) : vec2 p q 1 = q.2 := rfl

def rowAct (g : G) (q : F × F) : F × F :=
  (q.1 * (g : Mat) 0 0 + q.2 * (g : Mat) 1 0, q.1 * (g : Mat) 0 1 + q.2 * (g : Mat) 1 1)

theorem rowAct_apply (g : G) (q : F × F) :
    rowAct p g q = (q.1 * (g : Mat) 0 0 + q.2 * (g : Mat) 1 0, q.1 * (g : Mat) 0 1 + q.2 * (g : Mat) 1 1) := rfl

theorem vec2_rowAct (g : G) (q : F × F) : vec2 p (rowAct p g q) = Matrix.vecMul (vec2 p q) (g : Mat) := by
  funext j
  fin_cases j <;> simp [vec2, rowAct, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem continuous_rowAct (g : G) : Continuous (rowAct p g) := by
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)
  · exact (continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)

theorem measurable_rowAct (g : G) : Measurable (rowAct p g) := (continuous_rowAct p g).measurable

def rowActMatrix (g : G) : Mat := !![(g : Mat) 0 0, (g : Mat) 1 0; (g : Mat) 0 1, (g : Mat) 1 1]

theorem det_rowActMatrix (g : G) :
    (rowActMatrix p g).det = ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, rowActMatrix, Matrix.det_fin_two_of, Matrix.det_fin_two]
  ring

theorem det_rowActMatrix_ne_zero (g : G) : (rowActMatrix p g).det ≠ 0 := by
  rw [det_rowActMatrix]
  exact (Matrix.GeneralLinearGroup.det g).ne_zero

theorem rowAct_eq_comp (g : G) :
    rowAct p g = (MeasurableEquiv.finTwoArrow : (Fin 2 → F) ≃ᵐ F × F) ∘
      (fun f : Fin 2 → F => (rowActMatrix p g).mulVec f) ∘
        (MeasurableEquiv.finTwoArrow : (Fin 2 → F) ≃ᵐ F × F).symm := by
  funext q
  simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_symm_apply, MeasurableEquiv.finTwoArrow_apply,
    rowAct, rowActMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Fin.isValue]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

theorem measurable_mulVec_rowActMatrix (g : G) :
    Measurable (fun f : Fin 2 → F => (rowActMatrix p g).mulVec f) :=
  (continuous_const.matrix_mulVec continuous_id).measurable

theorem map_rowAct (g : G) :
    Measure.map (rowAct p g) ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) =
      ENNReal.ofReal ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖⁻¹ •
        ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  haveI : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  set μ : Measure F := selfDualHaarAt ℚ p with hμ
  set e : (Fin 2 → F) ≃ᵐ F × F := MeasurableEquiv.finTwoArrow with he
  have hpres : MeasurePreserving e (Measure.pi fun _ : Fin 2 => μ) (μ.prod μ) :=
    MeasureTheory.measurePreserving_finTwoArrow μ
  have hpi : Measure.map (fun f : Fin 2 → F => (rowActMatrix p g).mulVec f) (Measure.pi fun _ : Fin 2 => μ) =
      ENNReal.ofReal ‖(rowActMatrix p g).det‖⁻¹ • Measure.pi fun _ : Fin 2 => μ :=
    NumberField.AdicCompletion.map_matrix_mulVec_pi_eq_smul_pi ℚ p μ (rowActMatrix p g) (det_rowActMatrix_ne_zero p g)
  calc Measure.map (rowAct p g) (μ.prod μ)
      = Measure.map (rowAct p g) (Measure.map e (Measure.pi fun _ : Fin 2 => μ)) := by rw [hpres.map_eq]
    _ = Measure.map (rowAct p g ∘ e) (Measure.pi fun _ : Fin 2 => μ) :=
        Measure.map_map (measurable_rowAct p g) e.measurable
    _ = Measure.map (e ∘ fun f : Fin 2 → F => (rowActMatrix p g).mulVec f) (Measure.pi fun _ : Fin 2 => μ) := by
        congr 1
        rw [rowAct_eq_comp]
        funext f
        simp only [Function.comp_apply, ← he, MeasurableEquiv.symm_apply_apply]
    _ = Measure.map e (Measure.map (fun f : Fin 2 → F => (rowActMatrix p g).mulVec f)
          (Measure.pi fun _ : Fin 2 => μ)) :=
        (Measure.map_map e.measurable (measurable_mulVec_rowActMatrix p g)).symm
    _ = Measure.map e (ENNReal.ofReal ‖(rowActMatrix p g).det‖⁻¹ • Measure.pi fun _ : Fin 2 => μ) := by rw [hpi]
    _ = ENNReal.ofReal ‖(rowActMatrix p g).det‖⁻¹ • Measure.map e (Measure.pi fun _ : Fin 2 => μ) :=
        Measure.map_smul _ _ _
    _ = ENNReal.ofReal ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖⁻¹ • (μ.prod μ) := by
        rw [hpres.map_eq, det_rowActMatrix]

theorem integral_eq_norm_det_mul_integral_comp_rowAct (g : G) (K : F × F → ℂ) :
    ∫ q, K q ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) =
      (‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ : ℂ) *
        ∫ q, K (rowAct p g q) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  set μ2 : Measure (F × F) := (selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p) with hμ2
  set dg : F := ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) with hdg
  have hd0 : ‖dg‖ ≠ 0 := norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
  have hmap : Measure.map (rowAct p g) μ2 = ENNReal.ofReal ‖dg‖⁻¹ • μ2 := map_rowAct p g

  have hinv1 : ∀ q, rowAct p g⁻¹ (rowAct p g q) = q := by
    intro q
    have h : vec2 p (rowAct p g⁻¹ (rowAct p g q)) = vec2 p q := by
      rw [vec2_rowAct, vec2_rowAct, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.vecMul_one]
    exact Prod.ext (by simpa using congr_fun h 0) (by simpa using congr_fun h 1)
  have hinv2 : ∀ q, rowAct p g (rowAct p g⁻¹ q) = q := by
    intro q
    have h : vec2 p (rowAct p g (rowAct p g⁻¹ q)) = vec2 p q := by
      rw [vec2_rowAct, vec2_rowAct, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.vecMul_one]
    exact Prod.ext (by simpa using congr_fun h 0) (by simpa using congr_fun h 1)
  let e : F × F ≃ₜ F × F :=
    { toFun := rowAct p g, invFun := rowAct p g⁻¹, left_inv := hinv1, right_inv := hinv2,
      continuous_toFun := continuous_rowAct p g, continuous_invFun := continuous_rowAct p g⁻¹ }
  have hemb : MeasurableEmbedding (rowAct p g) := e.measurableEmbedding
  have hcomp : ∫ q, K (rowAct p g q) ∂μ2 = ∫ q, K q ∂(Measure.map (rowAct p g) μ2) :=
    (hemb.integral_map K).symm
  rw [hcomp, hmap, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg _)),
    Complex.real_smul, ← mul_assoc]
  have h1 : (‖dg‖ : ℂ) * ((‖dg‖⁻¹ : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_inv, mul_inv_cancel₀]
    exact_mod_cast hd0
  rw [h1, one_mul]

end ChangeOfVariables

section Algebra

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem det_unipotentGL2 (x : F) : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem coe_inv_unipotentGL2 (x : F) : (((unipotentGL2 x : G)⁻¹ : G) : Mat) = !![1, -x; 0, 1] := rfl

theorem inv_unipotentGL2 (x : F) : (unipotentGL2 x : G)⁻¹ = unipotentGL2 (-x) :=
  Units.ext (by rw [coe_inv_unipotentGL2, unipotentGL2_coe])

theorem transposeInvN_apply (g : G) (i j : Fin 2) : (transposeInvN (Fin 2) g : Mat) i j = ((g⁻¹ : G) : Mat) j i := by
  rw [coe_transposeInvN, Matrix.transpose_apply]

theorem transposeInvN_mul_unipotent_apply_one (h : G) (a : F) (i : Fin 2) :
    (transposeInvN (Fin 2) (h * unipotentGL2 a) : Mat) i 1 = (transposeInvN (Fin 2) h : Mat) i 1 := by
  rw [transposeInvN_apply, transposeInvN_apply, mul_inv_rev, Units.val_mul, coe_inv_unipotentGL2]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_mul_unipotent_apply_zero (h : G) (a : F) (i : Fin 2) :
    ((h * unipotentGL2 a : G) : Mat) i 0 = (h : Mat) i 0 := by
  rw [Units.val_mul, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_mul_unipotent_apply_one (h : G) (a : F) (i : Fin 2) :
    ((h * unipotentGL2 a : G) : Mat) i 1 = a * (h : Mat) i 0 + (h : Mat) i 1 := by
  rw [Units.val_mul, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem godementArg_e0 (k : G) (i : Fin 2) : godementArg p k i 0 = (k : Mat) i 0 :=
  godementArg_apply_castSucc p k i 0
theorem godementArg_e1 (k : G) (i : Fin 2) : godementArg p k i 1 = (k : Mat) i 1 :=
  godementArg_apply_castSucc p k i 1
theorem godementArg_e2 (k : G) (i : Fin 2) : godementArg p k i 2 = (transposeInvN (Fin 2) k : Mat) i 1 :=
  godementArg_apply_last p k i
theorem setCol2_e0 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) (i : Fin 2) : setCol23 p X 2 u i 0 = X i 0 := by
  simp [setCol23]
theorem setCol2_e1 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) (i : Fin 2) : setCol23 p X 2 u i 1 = X i 1 := by
  simp [setCol23]
theorem setCol2_e02 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) : setCol23 p X 2 u 0 2 = u.1 := by
  simp [setCol23]
theorem setCol2_e12 (X : Matrix (Fin 2) (Fin 3) F) (u : F × F) : setCol23 p X 2 u 1 2 = u.2 := by
  simp [setCol23]

theorem coe_transposeInvN_inv (h : G) (i j : Fin 2) : (transposeInvN (Fin 2) h⁻¹ : Mat) i j = (h : Mat) j i := by
  rw [transposeInvN_apply, inv_inv]

theorem norm_det_transposeInvN_inv (h : G) :
    ‖((Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) h⁻¹) : Fˣ) : F)‖ =
      ‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖ := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInvN, inv_inv,
    Matrix.det_transpose]

theorem setCol_godementArg_mul_unipotent_eq (h : G) (a : F) (v : F × F) :
    setCol23 p (godementArg p (h * unipotentGL2 a)) 2 (rowAct p (transposeInvN (Fin 2) h⁻¹) v) =
      ((h : G) : Mat) * !![1, a, v.1; 0, 1, v.2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [setCol2_e0, setCol2_e1, setCol2_e02, setCol2_e12, godementArg_e0, godementArg_e1,
      coe_mul_unipotent_apply_zero, coe_mul_unipotent_apply_one, rowAct, coe_transposeInvN_inv,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem rowAct_dot_transposeInv_col (h : G) (v : F × F) :
    (rowAct p (transposeInvN (Fin 2) h⁻¹) v).1 * (transposeInvN (Fin 2) h : Mat) 0 1 +
      (rowAct p (transposeInvN (Fin 2) h⁻¹) v).2 * (transposeInvN (Fin 2) h : Mat) 1 1 = v.2 := by
  have hm : ((h⁻¹ : G) : Mat) * (h : Mat) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e10 : ((h⁻¹ : G) : Mat) 1 0 * (h : Mat) 0 0 + ((h⁻¹ : G) : Mat) 1 1 * (h : Mat) 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congr_fun (congr_fun hm 1) 0
  have e11 : ((h⁻¹ : G) : Mat) 1 0 * (h : Mat) 0 1 + ((h⁻¹ : G) : Mat) 1 1 * (h : Mat) 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congr_fun (congr_fun hm 1) 1
  simp only [rowAct, coe_transposeInvN_inv, transposeInvN_apply]
  linear_combination v.1 * e10 + v.2 * e11

end Algebra

end GodFibre
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame.GodFibre"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame.GodFibre"

open GodFibre in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (θ : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hθn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → θ x = 1)
    (hθn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ θ x ≠ 1)
    (lam : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (Ψ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hΨsb : ∀ k : GL (Fin 2) (v.adicCompletion ℚ), IsSchwartzBruhat (fun X => Ψ X k))
    (hΨlaw : ∀ (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) (a : v.adicCompletion ℚ)
      (k : GL (Fin 2) (v.adicCompletion ℚ)), Ψ X (unipotentGL2 a * k) = θ a * Ψ X k)
    (M : GL (Fin 3) (v.adicCompletion ℚ)) (h : GL (Fin 2) (v.adicCompletion ℚ)) :
    letI := localBorel ℚ v
    ∫ a : v.adicCompletion ℚ,
        rowFourier23 v θ⁻¹
            (fun X => Ψ (X * ((M : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))
              (h * unipotentGL2 a)⁻¹)
            (godementArg v (h * unipotentGL2 a))
          * ((lam (Matrix.GeneralLinearGroup.det (h * unipotentGL2 a)) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det (h * unipotentGL2 a) : (v.adicCompletion ℚ)ˣ) :
              v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂(selfDualHaarAt ℚ v) =
      ((lam (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
        * ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ)
        * ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)
        * ∫ t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
            Ψ (((h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
                !![1, t.1, t.2.1; 0, 1, t.2.2] *
                ((M : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) h⁻¹ *
              θ (-(t.1 + t.2.2)) ∂(jacquetHaar3 v) := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI := isAddHaarMeasure_selfDualHaarAt v

  set Mm : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) := ((M : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) with hMm
  set hm : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := ((h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) with hhm
  set T01 : v.adicCompletion ℚ := (transposeInvN (Fin 2) h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 with hT01
  set T11 : v.adicCompletion ℚ := (transposeInvN (Fin 2) h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 with hT11
  set H : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ :=
    fun t => Ψ (hm * !![1, t.1, t.2.1; 0, 1, t.2.2] * Mm) h⁻¹ * θ (-(t.1 + t.2.2)) with hH
  set C : ℂ := ((lam (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)
        * ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ)
        * ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) with hC
  have hmod : ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) =
      ((‖((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
    rw [coe_modulus_eq_norm]

  have hpt : ∀ a : v.adicCompletion ℚ,
      rowFourier23 v θ⁻¹ (fun X => Ψ (X * Mm) (h * unipotentGL2 a)⁻¹) (godementArg v (h * unipotentGL2 a))
          * ((lam (Matrix.GeneralLinearGroup.det (h * unipotentGL2 a)) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det (h * unipotentGL2 a) : (v.adicCompletion ℚ)ˣ) :
              v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
        C * ∫ w : v.adicCompletion ℚ × v.adicCompletion ℚ, H (a, w) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) := by
    intro a
    have hdet : Matrix.GeneralLinearGroup.det (h * unipotentGL2 a) = Matrix.GeneralLinearGroup.det h := by
      rw [map_mul, det_unipotentGL2, mul_one]
    rw [hdet, rowFourier23_eq, colFourier23_apply, mul_inv_rev, inv_unipotentGL2]

    have hfun : (fun u : v.adicCompletion ℚ × v.adicCompletion ℚ =>
        Ψ (setCol23 v (godementArg v (h * unipotentGL2 a)) 2 u * Mm) (unipotentGL2 (-a) * h⁻¹) *
          θ⁻¹ (u.1 * godementArg v (h * unipotentGL2 a) 0 2 + u.2 * godementArg v (h * unipotentGL2 a) 1 2)) =
        fun u => θ (-a) * (Ψ (setCol23 v (godementArg v (h * unipotentGL2 a)) 2 u * Mm) h⁻¹ *
          θ⁻¹ (u.1 * T01 + u.2 * T11)) := by
      funext u
      rw [hΨlaw, godementArg_e2, godementArg_e2, transposeInvN_mul_unipotent_apply_one,
        transposeInvN_mul_unipotent_apply_one]
      ring
    rw [hfun, integral_const_mul]

    rw [integral_eq_norm_det_mul_integral_comp_rowAct v (transposeInvN (Fin 2) h⁻¹)
      (fun u : v.adicCompletion ℚ × v.adicCompletion ℚ =>
        Ψ (setCol23 v (godementArg v (h * unipotentGL2 a)) 2 u * Mm) h⁻¹ * θ⁻¹ (u.1 * T01 + u.2 * T11)),
      norm_det_transposeInvN_inv]
    have hfun2 : (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ =>
        Ψ (setCol23 v (godementArg v (h * unipotentGL2 a)) 2 (rowAct v (transposeInvN (Fin 2) h⁻¹) q) * Mm) h⁻¹ *
          θ⁻¹ ((rowAct v (transposeInvN (Fin 2) h⁻¹) q).1 * T01 + (rowAct v (transposeInvN (Fin 2) h⁻¹) q).2 * T11)) =
        fun q => Ψ (hm * !![1, a, q.1; 0, 1, q.2] * Mm) h⁻¹ * θ (-q.2) := by
      funext q
      rw [setCol_godementArg_mul_unipotent_eq, hT01, hT11, rowAct_dot_transposeInv_col, AddChar.inv_apply]
    rw [hfun2]

    have hH' : (fun w : v.adicCompletion ℚ × v.adicCompletion ℚ => H (a, w)) =
        fun w => θ (-a) * (Ψ (hm * !![1, a, w.1; 0, 1, w.2] * Mm) h⁻¹ * θ (-w.2)) := by
      funext w
      simp only [hH]
      rw [show -(a + w.2) = -a + -w.2 by ring, AddChar.map_add_eq_mul]
      ring
    rw [show (∫ w : v.adicCompletion ℚ × v.adicCompletion ℚ, H (a, w) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))) =
        θ (-a) * ∫ w : v.adicCompletion ℚ × v.adicCompletion ℚ,
          Ψ (hm * !![1, a, w.1; 0, 1, w.2] * Mm) h⁻¹ * θ (-w.2) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) by
      rw [show (fun w : v.adicCompletion ℚ × v.adicCompletion ℚ => H (a, w)) = _ from hH', integral_const_mul]]
    rw [hC, hmod]
    ring

  have hZc : Continuous fun t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (!![1, t.1, t.2.1; 0, 1, t.2.2] : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hAc : Continuous fun t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      hm * !![1, t.1, t.2.1; 0, 1, t.2.2] * Mm :=
    (continuous_const.matrix_mul hZc).matrix_mul continuous_const
  have hΨc : Continuous fun X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) => Ψ X h⁻¹ := (hΨsb h⁻¹).1.continuous
  have hθc : Continuous fun x : v.adicCompletion ℚ => (θ x : ℂ) := continuous_of_level v θ n hθn
  have hHc : Continuous H := by
    rw [hH]
    exact (hΨc.comp hAc).mul (hθc.comp ((continuous_fst.add (continuous_snd.comp continuous_snd)).neg))

  set P : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) :=
    fun X => ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * X *
      ((M⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) with hP
  set L : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
    fun X => (P X 0 1, (P X 0 2, P X 1 2)) with hL
  have hPc : Continuous P := by
    rw [hP]
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hLc : Continuous L := by
    rw [hL]
    exact (hPc.matrix_elem 0 1).prodMk ((hPc.matrix_elem 0 2).prodMk (hPc.matrix_elem 1 2))
  have hLA : ∀ t : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
      L (hm * !![1, t.1, t.2.1; 0, 1, t.2.2] * Mm) = t := by
    intro t
    have hkey : P (hm * !![1, t.1, t.2.1; 0, 1, t.2.2] * Mm) = !![1, t.1, t.2.1; 0, 1, t.2.2] := by
      have h1 : ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * hm = 1 := by
        rw [hhm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 : Mm * ((M⁻¹ : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = 1 := by
        rw [hMm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      simp only [hP]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
    simp only [hL, hkey]
    rfl
  have hHcs : HasCompactSupport H := by
    refine HasCompactSupport.intro ((hΨsb h⁻¹).2.image hLc) fun t ht => ?_
    have hnot : hm * !![1, t.1, t.2.1; 0, 1, t.2.2] * Mm ∉ tsupport (fun X => Ψ X h⁻¹) := by
      intro hmem
      exact ht ⟨_, hmem, hLA t⟩
    simp only [hH]
    rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul]
  have hHint : Integrable H ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))) :=
    hHc.integrable_of_hasCompactSupport hHcs

  have hLHS : (fun a : v.adicCompletion ℚ =>
      rowFourier23 v θ⁻¹ (fun X => Ψ (X * Mm) (h * unipotentGL2 a)⁻¹) (godementArg v (h * unipotentGL2 a))
          * ((lam (Matrix.GeneralLinearGroup.det (h * unipotentGL2 a)) : ℂˣ) : ℂ)
          * ((modulus ((Matrix.GeneralLinearGroup.det (h * unipotentGL2 a) : (v.adicCompletion ℚ)ˣ) :
              v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
      fun a => C * ∫ w : v.adicCompletion ℚ × v.adicCompletion ℚ, H (a, w) ∂((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)) :=
    funext hpt
  rw [hLHS, integral_const_mul, ← integral_prod H hHint]
  show C * ∫ t, H t ∂(jacquetHaar3 v) = _
  simp only [hC, hH, hhm, hMm]

end S_LanglandsTunnell_CubicInduction_integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integral_godementIntegrand_mul_unipotent_eq_mul_integral_frame (solution)
