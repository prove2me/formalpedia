-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetIntegral_principalSeries2_smooth_law_central_flip
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/8e219f10-e583-54e5-9431-92590156a14c

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetIntegral_principalSeries2_smooth_law_central_flip

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction UnramifiedWhittaker

namespace F6JacquetSlot

variable (p : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem isAddHaarMeasure_selfDualHaarAt :
    (selfDualHaarAt ℚ p : Measure (p.adicCompletion ℚ)).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm p.asIdeal : NNReal) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm p.asIdeal : NNReal) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure (p.adicCompletion ℚ))).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

theorem upperUnipotent2_mul_unipotent (x a : p.adicCompletion ℚ) :
    upperUnipotent2 p x * (unipotent a : GL (Fin 2) (p.adicCompletion ℚ)) = upperUnipotent2 p (x + a) := by
  refine Units.ext ?_
  simp only [Units.val_mul, upperUnipotent2_coe]
  show !![1, x; 0, 1] * !![1, a; 0, 1] = !![1, x + a; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipotentGL2_eq_unipotent (a : p.adicCompletion ℚ) :
    (unipotentGL2 a : GL (Fin 2) (p.adicCompletion ℚ)) = unipotent a := Units.ext rfl

theorem continuous_transposeInvN : Continuous (transposeInvN (Fin 2) : GL (Fin 2) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ)) := by
  have h1 : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      Matrix.transpose (((g⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) :=
    (Units.continuous_val.comp continuous_inv).matrix_transpose
  have h2 : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      Matrix.transpose (((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) :=
    Units.continuous_val.matrix_transpose
  exact Units.continuous_iff.mpr ⟨h1, h2⟩

theorem flip_identity (w₀p : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀p : ((w₀p : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (d : GL (Fin 2) (p.adicCompletion ℚ))
    (hd : ((d : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, 0; 0, -1])
    (t : p.adicCompletion ℚ) (k : GL (Fin 2) (p.adicCompletion ℚ)) :
    w₀p * transposeInvN (Fin 2) (d * (unipotent t * k)) = unipotent t * (w₀p * transposeInvN (Fin 2) (d * k)) := by
  have hd2 : d * d = 1 := by
    refine Units.ext ?_
    rw [Units.val_mul, hd, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hninv : (unipotent t : GL (Fin 2) (p.adicCompletion ℚ))⁻¹ = unipotent (-t) := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    simp only [Units.val_mul, Units.val_one]
    show !![(1 : p.adicCompletion ℚ), t; 0, 1] * !![1, -t; 0, 1] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hTd : ((transposeInvN (Fin 2) d : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![1, 0; 0, -1] := by
    rw [coe_transposeInvN, hdinv, hd]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  have hTn : ((transposeInvN (Fin 2) (unipotent t) : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, 0; -t, 1] := by
    rw [coe_transposeInvN, hninv]
    show Matrix.transpose !![(1 : p.adicCompletion ℚ), -t; 0, 1] = !![1, 0; -t, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  have hn : ((unipotent t : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
      !![1, t; 0, 1] := rfl
  rw [transposeInvN_mul, transposeInvN_mul, transposeInvN_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc (unipotent t),
    ← mul_assoc (unipotent t * w₀p)]
  congr 1
  refine Units.ext ?_
  simp only [Units.val_mul, hTd, hTn, hw₀p, hn]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem scalar_eq_diagonal2 (z : (p.adicCompletion ℚ)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) z = diagonal2 p ![z, z] := by
  refine Units.ext ?_
  rw [diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]

theorem scalar_mul_comm (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  rw [scalar_eq_diagonal2]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, mul_comm]

end F6JacquetSlot

open F6JacquetSlot in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : ((w₀p : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (d : GL (Fin 2) (p.adicCompletion ℚ)) (hd : ((d : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![1, 0; 0, -1]) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p

    (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φ (g * k) = φ g) ∧

    IsLocallyConstant (fun k : GL (Fin 2) (p.adicCompletion ℚ) => (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))) ∧

    (∀ (a : (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)), (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (unipotent a * k)) ∂(selfDualHaarAt ℚ p)) = NumberField.StandardAddChar.psiLocal ℚ p (-a) * (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))) ∧
    (∀ (a : (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)), (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (unipotentGL2 a * k)) ∂(selfDualHaarAt ℚ p)) = (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ a * (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))) ∧

    (∀ (zc : (p.adicCompletion ℚ)ˣ) (k : GL (Fin 2) (p.adicCompletion ℚ)),
      (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (Matrix.GeneralLinearGroup.scalar (Fin 2) zc * k)) ∂(selfDualHaarAt ℚ p)) = ((μ 0 zc : ℂˣ) : ℂ) * ((μ 1 zc : ℂˣ) : ℂ) * (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))) ∧

    (∀ (t : (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)), (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) (d * (unipotent t * k)))) ∂(selfDualHaarAt ℚ p)) = NumberField.StandardAddChar.psiLocal ℚ p (-t) * (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) (d * k))) ∂(selfDualHaarAt ℚ p))) ∧
    IsLocallyConstant (fun k : GL (Fin 2) (p.adicCompletion ℚ) => (∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (w₀p * transposeInvN (Fin 2) (d * k))) ∂(selfDualHaarAt ℚ p))) := by
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ p
  haveI : (selfDualHaarAt ℚ p : Measure (p.adicCompletion ℚ)).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨U, hUo, hU⟩ := exists_isOpen_forall_mul_eq_of_mem_principalSeries2 p μ φ hφ
  obtain ⟨hlc, hN, hT⟩ := mem_principalSeries2_iff.mp hφ

  set W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun k =>
    ∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
      φ (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p) with hW

  have hWU : ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g := by
    intro k hk g
    simp only [hW]
    congr 1
    funext x
    rw [← mul_assoc, hU k hk]

  have h1 : IsLocallyConstant W := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have ho : IsOpen {g' : GL (Fin 2) (p.adicCompletion ℚ) | g⁻¹ * g' ∈ U} :=
      hUo.preimage (continuous_const.mul continuous_id)
    filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ U by rw [inv_mul_cancel]; exact U.one_mem)] with g' hg'
    rw [show g' = g * (g⁻¹ * g') by rw [mul_inv_cancel_left], hWU _ hg']

  have h2 : ∀ (a : p.adicCompletion ℚ) (k : GL (Fin 2) (p.adicCompletion ℚ)),
      W (unipotent a * k) = NumberField.StandardAddChar.psiLocal ℚ p (-a) * W k := by
    intro a k
    simp only [hW]
    have hsub : (fun x : p.adicCompletion ℚ => NumberField.StandardAddChar.psiLocal ℚ p x *
        φ (antidiagonal2 p * upperUnipotent2 p x * (unipotent a * k))) =
        fun x => (fun y : p.adicCompletion ℚ => NumberField.StandardAddChar.psiLocal ℚ p (y - a) *
          φ (antidiagonal2 p * upperUnipotent2 p y * k)) (a + x) := by
      funext x
      dsimp only
      rw [add_sub_cancel_left, mul_assoc (antidiagonal2 p), ← mul_assoc (upperUnipotent2 p x), upperUnipotent2_mul_unipotent,
        ← mul_assoc, add_comm x a]
    have hmp : MeasurePreserving ((Homeomorph.addLeft a).toMeasurableEquiv : p.adicCompletion ℚ ≃ᵐ p.adicCompletion ℚ)
        (selfDualHaarAt ℚ p) (selfDualHaarAt ℚ p) := by
      refine ⟨(Homeomorph.addLeft a).toMeasurableEquiv.measurable, ?_⟩
      have := map_add_left_eq_self (selfDualHaarAt ℚ p : Measure (p.adicCompletion ℚ)) a
      simpa [Homeomorph.toMeasurableEquiv_coe] using this
    have hint := hmp.integral_comp (Homeomorph.addLeft a).toMeasurableEquiv.measurableEmbedding
      (fun y : p.adicCompletion ℚ => NumberField.StandardAddChar.psiLocal ℚ p (y - a) * φ (antidiagonal2 p * upperUnipotent2 p y * k))
    simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.coe_addLeft] at hint
    rw [hsub, hint, ← integral_const_mul]
    congr 1
    funext y
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  refine ⟨⟨U, hUo, hU⟩, h1, h2, ?_, ?_, ?_, ?_⟩
  ·
    intro a k
    rw [unipotentGL2_eq_unipotent, AddChar.inv_apply]
    exact h2 a k
  ·
    intro zc k
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [← mul_assoc (antidiagonal2 p * upperUnipotent2 p x), scalar_mul_comm, scalar_eq_diagonal2, mul_assoc (diagonal2 p _), hT]
    have hz : ‖((zc : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)‖ ≠ 0 := norm_ne_zero_iff.mpr (Units.ne_zero _)
    have hc : torusChar2 p μ ![zc, zc] * halfModulus2 p ![zc, zc] = ((μ 0 zc : ℂˣ) : ℂ) * ((μ 1 zc : ℂˣ) : ℂ) := by
      simp [torusChar2, halfModulus2, Fin.prod_univ_two]
    rw [hc]
    ring
  ·
    intro t k
    have hflip := flip_identity p w₀p hw₀p d hd t k
    have h4 := h2 t (w₀p * transposeInvN (Fin 2) (d * k))
    rw [hflip]
    exact h4
  ·
    have h5 := h1.comp_continuous
      (continuous_const.mul ((continuous_transposeInvN p).comp (continuous_const.mul continuous_id)) :
        Continuous fun k : GL (Fin 2) (p.adicCompletion ℚ) => w₀p * transposeInvN (Fin 2) (d * k))
    exact h5

end S_LanglandsTunnell_CubicInduction_jacquetIntegral_principalSeries2_smooth_law_central_flip
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetIntegral_principalSeries2_smooth_law_central_flip (solution)
