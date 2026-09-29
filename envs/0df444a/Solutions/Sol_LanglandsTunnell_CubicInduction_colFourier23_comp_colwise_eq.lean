-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.colFourier23_comp_colwise_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6c30ffb6-54a3-59b1-a142-b1b61a9c2661

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_AdicCompletion_map_matrix_mulVec_pi_eq_smul_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_colFourier23_comp_colwise_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

noncomputable section

open scoped Matrix

namespace ColCov

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm p.asIdeal : NNReal) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm p.asIdeal : NNReal) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure F)).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

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

theorem coe_transposeInvN_inv (B : G) : ((transposeInvN (Fin 2) B⁻¹ : G) : Mat) = ((B : G) : Mat)ᵀ := by
  rw [coe_transposeInvN, inv_inv]

theorem rowAct_transpose (B : G) (u : F × F) :
    rowAct p (transposeInvN (Fin 2) B⁻¹) u =
      ((B : Mat) 0 0 * u.1 + (B : Mat) 0 1 * u.2, (B : Mat) 1 0 * u.1 + (B : Mat) 1 1 * u.2) := by
  rw [rowAct_apply]
  simp only [coe_transposeInvN_inv, Matrix.transpose_apply]
  exact Prod.ext (by ring) (by ring)

theorem det_transposeInvN_inv (B : G) :
    ((Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) B⁻¹) : Fˣ) : F) =
      ((Matrix.GeneralLinearGroup.det B : Fˣ) : F) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInvN_inv]
  exact Matrix.det_transpose _

end ColCov
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_colFourier23_comp_colwise_eq.ColCov"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_colFourier23_comp_colwise_eq.ColCov"

open ColCov in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (j : Fin 3)
    (A : Fin 3 → GL (Fin 2) (v.adicCompletion ℚ))
    (ρ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) :
    colFourier23 v η j (fun Y => ρ (Matrix.of fun i k =>
        ∑ i' : Fin 2, ((A k : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i i' * Y i' k)) X =
      ((modulus ((Matrix.GeneralLinearGroup.det (A j) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ *
        colFourier23 v η j ρ (Matrix.of fun i k =>
          ∑ i' : Fin 2, ((Function.update A j (transposeInvN (Fin 2) (A j)) k : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i i' * X i' k) := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v

  set B : GL (Fin 2) (v.adicCompletion ℚ) := A j with hB
  set Z : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) := Matrix.of fun i k =>
      ∑ i' : Fin 2, ((Function.update A j (transposeInvN (Fin 2) (A j)) k : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i i' * X i' k with hZ
  rw [colFourier23_apply, colFourier23_apply]

  set K : v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ := fun w =>
    ρ (setCol23 v Z j w) * η (w.1 * Z 0 j + w.2 * Z 1 j) with hK

  have hZj : ∀ i, Z i j = ∑ i' : Fin 2, ((transposeInvN (Fin 2) B : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i i' * X i' j := by
    intro i; rw [hZ, Matrix.of_apply, Function.update_self, hB]
  have hZk : ∀ i k, k ≠ j → Z i k = ∑ i' : Fin 2, ((A k : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i i' * X i' k := by
    intro i k hk; rw [hZ, Matrix.of_apply, Function.update_of_ne hk]

  have hmat : ∀ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
      (Matrix.of fun i k => ∑ i' : Fin 2, ((A k : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i i' * setCol23 v X j u i' k) =
      setCol23 v Z j (rowAct v (transposeInvN (Fin 2) B⁻¹) u) := by
    intro u
    ext i k
    rw [Matrix.of_apply, setCol23_apply, rowAct_transpose]
    by_cases hk : k = j
    · subst hk
      simp only [setCol23_apply, if_true, Fin.sum_univ_two, hB,
        show ((0 : Fin 2) = 0) = True from by decide, show ((1 : Fin 2) = 0) = False from by decide, if_false]
      fin_cases i
      · simp
      · simp
    · simp only [setCol23_apply, if_neg hk, hZk i k hk]

  have hBinv : (((B⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
      ((B : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hker : ∀ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
      (rowAct v (transposeInvN (Fin 2) B⁻¹) u).1 * Z 0 j + (rowAct v (transposeInvN (Fin 2) B⁻¹) u).2 * Z 1 j =
        u.1 * X 0 j + u.2 * X 1 j := by
    intro u
    have e00 := congr_fun (congr_fun hBinv 0) 0
    have e01 := congr_fun (congr_fun hBinv 0) 1
    have e10 := congr_fun (congr_fun hBinv 1) 0
    have e11 := congr_fun (congr_fun hBinv 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e00 e01 e10 e11
    rw [rowAct_transpose, hZj 0, hZj 1]
    simp only [Fin.sum_univ_two, coe_transposeInvN, Matrix.transpose_apply]

    linear_combination (u.1 * X 0 j) * e00 + (u.2 * X 0 j) * e01 + (u.1 * X 1 j) * e10 + (u.2 * X 1 j) * e11
  have hint : ∀ u : v.adicCompletion ℚ × v.adicCompletion ℚ,
      ρ (Matrix.of fun i k => ∑ i' : Fin 2, ((A k : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i i' * setCol23 v X j u i' k) * η (u.1 * X 0 j + u.2 * X 1 j) =
      K (rowAct v (transposeInvN (Fin 2) B⁻¹) u) := by
    intro u
    rw [hK]
    simp only
    rw [hmat u, hker u]
  simp_rw [hint]

  have hcov := integral_eq_norm_det_mul_integral_comp_rowAct v (transposeInvN (Fin 2) B⁻¹) K
  rw [det_transposeInvN_inv] at hcov
  have hd0 : (‖((Matrix.GeneralLinearGroup.det B : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det B).ne_zero
  have hmod : ((modulus ((Matrix.GeneralLinearGroup.det (A j) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)
      = (‖((Matrix.GeneralLinearGroup.det B : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ : ℂ) := by
    rw [← hB, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v, coe_nnnorm]
  rw [hmod, eq_inv_mul_iff_mul_eq₀ hd0, ← hcov]

end S_LanglandsTunnell_CubicInduction_colFourier23_comp_colwise_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_colFourier23_comp_colwise_eq (solution)
