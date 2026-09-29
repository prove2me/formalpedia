-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e308532a-ec78-5c95-953b-e8ae677ed95f

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_CharConductor
import Theorems.Thm_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Theorems.Thm_LocalNewvector_finiteDimensional_principalSeries_inf_rightInvariantFunctions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace LeviRestriction
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private noncomputable def leviNorm (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) : ℂ :=
  ((‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ)

private noncomputable def restrictFn (v : HeightOneSpectrum (𝓞 ℚ))
    (f : LocalGL3 v → ℂ) (m : GL (Fin 2) (v.adicCompletion ℚ)) : ℂ :=
  leviNorm v m * f (iotaGL m)

private theorem det_norm_pos (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    0 < ‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ :=
  norm_pos_iff.mpr ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit m)).ne_zero

private theorem leviNorm_mul (v : HeightOneSpectrum (𝓞 ℚ)) (m A : GL (Fin 2) (v.adicCompletion ℚ)) :
    leviNorm v (m * A) =
      leviNorm v m * ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) := by
  unfold leviNorm
  rw [Units.val_mul, Matrix.det_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_mul]

private theorem det_rpow_half_mul_neg_half (v : HeightOneSpectrum (𝓞 ℚ)) (A : GL (Fin 2) (v.adicCompletion ℚ)) :
    ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
        ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Real.rpow_add (det_norm_pos v A), add_neg_cancel, Real.rpow_zero, Complex.ofReal_one]

private theorem exists_radical_mul_of_block (v : HeightOneSpectrum (𝓞 ℚ))
    (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ))
    (c : (v.adicCompletion ℚ)ˣ)
    (h20 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0)
    (h22 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ))
    (hblock : ∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) :
    ∃ y z : v.adicCompletion ℚ, p = upperUnipotent3 0 y z * (iotaGL A * diagonal3 v ![1, 1, c]) := by
  have h00 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 := hblock 0 0
  have h01 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 := hblock 0 1
  have h10 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 := hblock 1 0
  have h11 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 := hblock 1 1
  refine ⟨(p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2 * ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ),
    (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2 * ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ),
    Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, upperUnipotent3_coe, coe_iotaGL, diagonal3_coe]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.diagonal, h00, h01, h10, h11, h20, h21, h22]

private theorem iotaGL_mul_radical (v : HeightOneSpectrum (𝓞 ℚ))
    (m : GL (Fin 2) (v.adicCompletion ℚ)) (y z : v.adicCompletion ℚ) :
    iotaGL m * upperUnipotent3 0 y z =
      upperUnipotent3 0
        ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 * z +
          (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 * y)
        ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 * z +
          (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 * y) * iotaGL m := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, upperUnipotent3_coe, upperUnipotent3_coe, coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem iotaGL_mul_center (v : HeightOneSpectrum (𝓞 ℚ))
    (m : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ) :
    iotaGL m * diagonal3 v ![1, 1, c] = diagonal3 v ![1, 1, c] * iotaGL m := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_iotaGL, diagonal3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Matrix.diagonal]

private theorem torusChar3_center (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (c : (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ ![1, 1, c] = ((χ 2 c : ℂˣ) : ℂ) := by
  simp [torusChar3, Fin.prod_univ_three]

private theorem halfModulus3_center (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v ![1, 1, c] = ((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) := by
  simp [halfModulus3]

private theorem restrictFn_rightTranslate (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ))
    (c : (v.adicCompletion ℚ)ˣ)
    (h20 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0)
    (h22 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ))
    (hblock : ∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j)
    (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    restrictFn v (gl3AmbientRightTranslate (R := ℂ) p f) m =
      ((χ 2 c : ℂˣ) : ℂ) * ((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) *
        ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
        restrictFn v f (m * A) := by
  obtain ⟨y, z, hp⟩ := exists_radical_mul_of_block v p A c h20 h21 h22 hblock
  simp only [restrictFn, gl3AmbientRightTranslate_apply]
  rw [hp, ← mul_assoc (iotaGL m), iotaGL_mul_radical, mul_assoc,
    apply_upperUnipotent3_mul_of_mem_principalSeries3 hf, ← mul_assoc, ← map_mul, iotaGL_mul_center,
    apply_diagonal3_mul_of_mem_principalSeries3 hf, torusChar3_center, halfModulus3_center, leviNorm_mul]
  have hdet := det_rpow_half_mul_neg_half v A
  generalize ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) = Dp at hdet ⊢
  generalize ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) = Dm at hdet ⊢
  linear_combination (-(leviNorm v m * ((χ 2 c : ℂˣ) : ℂ) * ((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) *
    f (iotaGL (m * A)))) * hdet

private theorem iotaGL_eq_upperUnipotent3_of_unipotent (v : HeightOneSpectrum (𝓞 ℚ))
    (u : GL (Fin 2) (v.adicCompletion ℚ))
    (hu00 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 = 1)
    (hu11 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1)
    (hu10 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0) :
    iotaGL u = upperUnipotent3 ((u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) 0 0 := by
  apply Units.ext
  rw [coe_iotaGL, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, hu00, hu11, hu10]

private theorem det_eq_one_of_unipotent (v : HeightOneSpectrum (𝓞 ℚ)) (u : GL (Fin 2) (v.adicCompletion ℚ))
    (hu00 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 = 1)
    (hu11 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1)
    (hu10 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0) :
    (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
  rw [Matrix.det_fin_two, hu00, hu11, hu10]
  ring

private theorem restrictFn_unipotent_mul (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (u : GL (Fin 2) (v.adicCompletion ℚ))
    (hu00 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 = 1)
    (hu11 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1)
    (hu10 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0)
    (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    restrictFn v f (u * m) = restrictFn v f m := by
  unfold restrictFn
  rw [map_mul, iotaGL_eq_upperUnipotent3_of_unipotent v u hu00 hu11 hu10,
    apply_upperUnipotent3_mul_of_mem_principalSeries3 hf]
  congr 1
  unfold leviNorm
  rw [Units.val_mul, Matrix.det_mul, det_eq_one_of_unipotent v u hu00 hu11 hu10, one_mul]

private theorem iotaGL_eq_diagonal3_of_diagonal (v : HeightOneSpectrum (𝓞 ℚ)) (d : GL (Fin 2) (v.adicCompletion ℚ))
    (a₀ a₁ : (v.adicCompletion ℚ)ˣ)
    (hd : (d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(a₀ : v.adicCompletion ℚ), (a₁ : v.adicCompletion ℚ)]) :
    iotaGL d = diagonal3 v ![a₀, a₁, 1] := by
  apply Units.ext
  rw [coe_iotaGL, diagonal3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, hd, Matrix.diagonal]

private theorem torusChar3_diagonal (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₀ a₁ : (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ ![a₀, a₁, 1] = ((χ 0 a₀ : ℂˣ) : ℂ) * ((χ 1 a₁ : ℂˣ) : ℂ) := by
  simp [torusChar3, Fin.prod_univ_three]

private theorem halfModulus3_diagonal (v : HeightOneSpectrum (𝓞 ℚ)) (a₀ a₁ : (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v ![a₀, a₁, 1] = ((‖(a₀ : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
  simp [halfModulus3]

private theorem mul_rpow_neg_half_eq_sqrt_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * (x * y) ^ (-((1 : ℝ) / 2)) = Real.sqrt (x / y) := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow hx.le hy.le, Real.mul_rpow hx.le hy.le, Real.rpow_neg hx.le,
    Real.rpow_neg hy.le]
  have hx2 : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
    rw [← Real.rpow_add hx]
    norm_num
  have ha0 : x ^ ((1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  set a := x ^ ((1 : ℝ) / 2)
  rw [← hx2, div_eq_mul_inv a, mul_mul_mul_comm, mul_inv_cancel₀ ha0, one_mul]

private theorem restrictFn_diagonal_mul (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (d : GL (Fin 2) (v.adicCompletion ℚ)) (a₀ a₁ : (v.adicCompletion ℚ)ˣ)
    (hd : (d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(a₀ : v.adicCompletion ℚ), (a₁ : v.adicCompletion ℚ)])
    (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    restrictFn v f (d * m) =
      ((χ 0 a₀ : ℂˣ) : ℂ) * ((χ 1 a₁ : ℂˣ) : ℂ) *
        ((Real.sqrt (‖(a₀ : v.adicCompletion ℚ)‖ / ‖(a₁ : v.adicCompletion ℚ)‖) : ℝ) : ℂ) * restrictFn v f m := by
  unfold restrictFn
  rw [map_mul, iotaGL_eq_diagonal3_of_diagonal v d a₀ a₁ hd, apply_diagonal3_mul_of_mem_principalSeries3 hf,
    torusChar3_diagonal, halfModulus3_diagonal]
  have hsplit : leviNorm v (d * m) =
      ((‖(d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) * leviNorm v m := by
    unfold leviNorm
    rw [Units.val_mul, Matrix.det_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_mul]
  have hdet : (d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det =
      (a₀ : v.adicCompletion ℚ) * (a₁ : v.adicCompletion ℚ) := by
    rw [hd, Matrix.det_fin_two]
    simp
  have hkey : ((‖(a₀ : v.adicCompletion ℚ)‖ : ℝ) : ℂ) *
      ((‖(d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) =
      ((Real.sqrt (‖(a₀ : v.adicCompletion ℚ)‖ / ‖(a₁ : v.adicCompletion ℚ)‖) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hdet, norm_mul,
      mul_rpow_neg_half_eq_sqrt_div (norm_pos_iff.mpr a₀.ne_zero) (norm_pos_iff.mpr a₁.ne_zero)]
  rw [hsplit, ← hkey]
  ring

private theorem continuous_iotaGL (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous (iotaGL : GL (Fin 2) (v.adicCompletion ℚ) →* LocalGL3 v) := by
  rw [Units.continuous_iff]
  constructor
  · apply continuous_matrix
    intro i j
    simp only [Function.comp_apply, coe_iotaGL, embedMat2]
    fin_cases i <;> fin_cases j <;>
      first
      | exact continuous_const
      | exact Units.continuous_val.matrix_elem 0 0
      | exact Units.continuous_val.matrix_elem 0 1
      | exact Units.continuous_val.matrix_elem 1 0
      | exact Units.continuous_val.matrix_elem 1 1
  · apply continuous_matrix
    intro i j
    simp only [← map_inv, coe_iotaGL, embedMat2]
    fin_cases i <;> fin_cases j <;>
      first
      | exact continuous_const
      | exact Units.continuous_coe_inv.matrix_elem 0 0
      | exact Units.continuous_coe_inv.matrix_elem 0 1
      | exact Units.continuous_coe_inv.matrix_elem 1 0
      | exact Units.continuous_coe_inv.matrix_elem 1 1

private theorem isLocallyConstant_leviNorm (v : HeightOneSpectrum (𝓞 ℚ)) : IsLocallyConstant (leviNorm v) := by
  have hnorm : IsLocallyConstant fun m : GL (Fin 2) (v.adicCompletion ℚ) =>
      ‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro m
    have hc : ContinuousAt (fun m : GL (Fin 2) (v.adicCompletion ℚ) =>
        (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det) m :=
      (Units.continuous_val.matrix_det).continuousAt
    exact hc.eventually (eventually_norm_eq v ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit m)).ne_zero)
  exact hnorm.comp fun r : ℝ => ((r ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ)

private theorem isLocallyConstant_restrictFn (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) : IsLocallyConstant (restrictFn v f) :=
  (isLocallyConstant_leviNorm v).mul
    ((isLocallyConstant_of_mem_principalSeries3 hf).comp_continuous (continuous_iotaGL v))

private noncomputable def schurBlock (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
  !![gl3Entry v g 0 0 - gl3Entry v g 0 2 * gl3Entry v g 2 0 / gl3Entry v g 2 2,
      gl3Entry v g 0 1 - gl3Entry v g 0 2 * gl3Entry v g 2 1 / gl3Entry v g 2 2;
    gl3Entry v g 1 0 - gl3Entry v g 1 2 * gl3Entry v g 2 0 / gl3Entry v g 2 2,
      gl3Entry v g 1 1 - gl3Entry v g 1 2 * gl3Entry v g 2 1 / gl3Entry v g 2 2]

private theorem schurBlock_det (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v} (hg : gl3Entry v g 2 2 ≠ 0) :
    (schurBlock v g).det = gl3Det v g / gl3Entry v g 2 2 := by
  unfold schurBlock gl3Det
  rw [Matrix.det_fin_two_of, Matrix.det_fin_three]
  simp only [gl3Entry] at hg ⊢
  field_simp
  ring

private theorem schurBlock_det_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v}
    (hg : gl3Entry v g 2 2 ≠ 0) : (schurBlock v g).det ≠ 0 := by
  rw [schurBlock_det v hg]
  exact div_ne_zero (gl3Det_ne_zero v g) hg

private noncomputable def schurGL (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v} (hg : gl3Entry v g 2 2 ≠ 0) :
    GL (Fin 2) (v.adicCompletion ℚ) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (schurBlock v g) (schurBlock_det_ne_zero v hg)

private theorem schurGL_coe (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v} (hg : gl3Entry v g 2 2 ≠ 0) :
    ((schurGL v hg : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      schurBlock v g := rfl

private noncomputable def lowerRatio (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (i : Fin 2) :
    v.adicCompletion ℚ :=
  gl3Entry v g 2 (Fin.castSucc i) / gl3Entry v g 2 2

private noncomputable def bigCell (v : HeightOneSpectrum (𝓞 ℚ)) : Set (LocalGL3 v) :=
  {g | gl3Entry v g 2 2 ≠ 0 ∧ ∀ i : Fin 2, Valued.v (lowerRatio v g i) ≤ 1}

private noncomputable def sectionValue (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (g : LocalGL3 v) : ℂ := by
  classical exact
    if hg : gl3Entry v g 2 2 ≠ 0 then
      TateLocal.charExt (χ 2) (gl3Entry v g 2 2) * ((‖gl3Entry v g 2 2‖⁻¹ : ℝ) : ℂ) *
        ((‖(schurBlock v g).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * φ (schurGL v hg)
    else 0

private noncomputable def sectionFn (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) : LocalGL3 v → ℂ :=
  (bigCell v).indicator (sectionValue v χ φ)

private theorem sectionValue_of_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) {g : LocalGL3 v} (hg : gl3Entry v g 2 2 ≠ 0) :
    sectionValue v χ φ g =
      TateLocal.charExt (χ 2) (gl3Entry v g 2 2) * ((‖gl3Entry v g 2 2‖⁻¹ : ℝ) : ℂ) *
        ((‖(schurBlock v g).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * φ (schurGL v hg) := by
  unfold sectionValue
  rw [dif_pos hg]

private theorem gl3Entry_iotaGL (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) (i j : Fin 3) :
    gl3Entry v (iotaGL m) i j = embedMat2 (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j := by
  simp [gl3Entry]

private theorem schurBlock_iotaGL (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    schurBlock v (iotaGL m) = (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [schurBlock, gl3Entry_iotaGL, embedMat2]

private theorem corner_iotaGL (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    gl3Entry v (iotaGL m) 2 2 = 1 := by
  simp [gl3Entry_iotaGL, embedMat2]

private theorem schurGL_iotaGL (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ))
    (h : gl3Entry v (iotaGL m) 2 2 ≠ 0) : schurGL v h = m := by
  apply Units.ext
  rw [schurGL_coe, schurBlock_iotaGL]

private theorem iotaGL_mem_bigCell (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    iotaGL m ∈ bigCell v := by
  refine ⟨by rw [corner_iotaGL]; exact one_ne_zero, fun i => ?_⟩
  fin_cases i <;> simp [lowerRatio, gl3Entry_iotaGL, embedMat2]

private theorem sectionFn_iotaGL (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    sectionFn v χ φ (iotaGL m) =
      ((‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * φ m := by
  have h1 : gl3Entry v (iotaGL m) 2 2 ≠ 0 := by rw [corner_iotaGL]; exact one_ne_zero
  rw [sectionFn, Set.indicator_of_mem (iotaGL_mem_bigCell v m), sectionValue_of_ne_zero v χ φ h1,
    schurGL_iotaGL v m h1, schurBlock_iotaGL]
  have hc : TateLocal.charExt (χ 2) (gl3Entry v (iotaGL m) 2 2) = 1 := by
    rw [corner_iotaGL, TateLocal.charExt_of_ne_zero (χ 2) one_ne_zero]
    simp
  rw [hc, corner_iotaGL]
  simp

private theorem restrictFn_sectionFn (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    restrictFn v (sectionFn v χ φ) m = φ m := by
  rw [restrictFn, sectionFn_iotaGL, leviNorm, ← mul_assoc, mul_comm
    ((‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ),
    det_rpow_half_mul_neg_half, one_mul]

private theorem sectionValue_add (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ ψ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (g : LocalGL3 v) :
    sectionValue v χ (φ + ψ) g = sectionValue v χ φ g + sectionValue v χ ψ g := by
  unfold sectionValue
  split_ifs with hg
  · simp only [Pi.add_apply]
    ring
  · simp

private theorem sectionValue_smul (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (a : ℂ) (φ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (g : LocalGL3 v) :
    sectionValue v χ (a • φ) g = a * sectionValue v χ φ g := by
  unfold sectionValue
  split_ifs with hg
  · simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · simp

private theorem sectionFn_add (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ ψ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) :
    sectionFn v χ (φ + ψ) = sectionFn v χ φ + sectionFn v χ ψ := by
  funext g
  by_cases hg : g ∈ bigCell v
  · simp only [sectionFn, Pi.add_apply, Set.indicator_of_mem hg, sectionValue_add]
  · simp only [sectionFn, Pi.add_apply, Set.indicator_of_notMem hg, add_zero]

private theorem sectionFn_smul (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (a : ℂ) (φ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) :
    sectionFn v χ (a • φ) = a • sectionFn v χ φ := by
  funext g
  by_cases hg : g ∈ bigCell v
  · simp only [sectionFn, Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem hg, sectionValue_smul]
  · simp only [sectionFn, Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hg, mul_zero]

private noncomputable def unip2 (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    GL (Fin 2) (v.adicCompletion ℚ) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by rw [Matrix.det_fin_two_of]; simp)

private theorem unip2_coe (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    ((unip2 v x : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      !![1, x; 0, 1] := rfl

private noncomputable def diag2 (v : HeightOneSpectrum (𝓞 ℚ)) (a₀ a₁ : (v.adicCompletion ℚ)ˣ) :
    GL (Fin 2) (v.adicCompletion ℚ) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![(a₀ : v.adicCompletion ℚ), (a₁ : v.adicCompletion ℚ)])
    (by rw [Matrix.det_diagonal, Fin.prod_univ_two]; simp)

private theorem diag2_coe (v : HeightOneSpectrum (𝓞 ℚ)) (a₀ a₁ : (v.adicCompletion ℚ)ˣ) :
    ((diag2 v a₀ a₁ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(a₀ : v.adicCompletion ℚ), (a₁ : v.adicCompletion ℚ)] := rfl

private theorem gl3Entry_unipotent_mul_bottom (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) (j : Fin 3) : gl3Entry v (upperUnipotent3 x y z * g) 2 j = gl3Entry v g 2 j := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_unipotent_mul_upper (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) (j : Fin 3) :
    gl3Entry v (upperUnipotent3 x y z * g) 0 j = gl3Entry v g 0 j + x * gl3Entry v g 1 j + z * gl3Entry v g 2 j ∧
      gl3Entry v (upperUnipotent3 x y z * g) 1 j = gl3Entry v g 1 j + y * gl3Entry v g 2 j := by
  constructor <;> simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem lowerRatio_unipotent_mul (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) (i : Fin 2) : lowerRatio v (upperUnipotent3 x y z * g) i = lowerRatio v g i := by
  simp only [lowerRatio, gl3Entry_unipotent_mul_bottom]

private theorem unipotent_mul_mem_bigCell_iff (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) : upperUnipotent3 x y z * g ∈ bigCell v ↔ g ∈ bigCell v := by
  simp only [bigCell, Set.mem_setOf_eq, gl3Entry_unipotent_mul_bottom, lowerRatio_unipotent_mul]

private theorem schurBlock_unipotent_mul (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : v.adicCompletion ℚ) {g : LocalGL3 v}
    (hg : gl3Entry v g 2 2 ≠ 0) :
    schurBlock v (upperUnipotent3 x y z * g) = !![1, x; 0, 1] * schurBlock v g := by
  have h0 := fun j => (gl3Entry_unipotent_mul_upper v x y z g j).1
  have h1 := fun j => (gl3Entry_unipotent_mul_upper v x y z g j).2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [schurBlock, gl3Entry_unipotent_mul_bottom, h0, h1, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

private theorem schurGL_unipotent_mul (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : v.adicCompletion ℚ) {g : LocalGL3 v}
    (hg : gl3Entry v g 2 2 ≠ 0) (hg' : gl3Entry v (upperUnipotent3 x y z * g) 2 2 ≠ 0) :
    schurGL v hg' = unip2 v x * schurGL v hg := by
  apply Units.ext
  rw [Units.val_mul, schurGL_coe, schurGL_coe, unip2_coe, schurBlock_unipotent_mul v x y z hg]

private theorem sectionFn_unipotent_mul (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {φ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ}
    (hφ : ∀ (u : GL (Fin 2) (v.adicCompletion ℚ)), (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 = 1 →
      (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1 →
      (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0 → ∀ m, φ (u * m) = φ m)
    (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    sectionFn v χ φ (upperUnipotent3 x y z * g) = sectionFn v χ φ g := by
  unfold sectionFn
  by_cases hmem : g ∈ bigCell v
  · rw [Set.indicator_of_mem ((unipotent_mul_mem_bigCell_iff v x y z g).mpr hmem), Set.indicator_of_mem hmem]
    have hg : gl3Entry v g 2 2 ≠ 0 := hmem.1
    have hg' : gl3Entry v (upperUnipotent3 x y z * g) 2 2 ≠ 0 := by rwa [gl3Entry_unipotent_mul_bottom]
    rw [sectionValue_of_ne_zero v χ φ hg', sectionValue_of_ne_zero v χ φ hg, schurGL_unipotent_mul v x y z hg hg',
      hφ (unip2 v x) (by simp [unip2_coe]) (by simp [unip2_coe]) (by simp [unip2_coe]),
      gl3Entry_unipotent_mul_bottom, schurBlock_unipotent_mul v x y z hg, Matrix.det_mul, Matrix.det_fin_two_of]
    simp
  · rw [Set.indicator_of_notMem (fun h => hmem ((unipotent_mul_mem_bigCell_iff v x y z g).mp h)),
      Set.indicator_of_notMem hmem]

private theorem gl3Entry_diagonal_mul (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) (i j : Fin 3) :
    gl3Entry v (diagonal3 v a * g) i j = (a i : v.adicCompletion ℚ) * gl3Entry v g i j := by
  simp [gl3Entry, Matrix.diagonal_mul]

private theorem lowerRatio_diagonal_mul (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) (i : Fin 2) : lowerRatio v (diagonal3 v a * g) i = lowerRatio v g i := by
  simp only [lowerRatio, gl3Entry_diagonal_mul]
  rw [mul_div_mul_left _ _ (a 2).ne_zero]

private theorem diagonal_mul_mem_bigCell_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) : diagonal3 v a * g ∈ bigCell v ↔ g ∈ bigCell v := by
  simp only [bigCell, Set.mem_setOf_eq, gl3Entry_diagonal_mul, lowerRatio_diagonal_mul, mul_ne_zero_iff,
    ne_eq, Units.ne_zero, not_false_eq_true, true_and]

private theorem schurBlock_diagonal_mul (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    {g : LocalGL3 v} (hg : gl3Entry v g 2 2 ≠ 0) :
    schurBlock v (diagonal3 v a * g) =
      Matrix.diagonal ![(a 0 : v.adicCompletion ℚ), (a 1 : v.adicCompletion ℚ)] * schurBlock v g := by
  have ha : (a 2 : v.adicCompletion ℚ) ≠ 0 := (a 2).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [schurBlock, gl3Entry_diagonal_mul, Matrix.diagonal_mul] <;> field_simp

private theorem schurGL_diagonal_mul (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    {g : LocalGL3 v} (hg : gl3Entry v g 2 2 ≠ 0) (hg' : gl3Entry v (diagonal3 v a * g) 2 2 ≠ 0) :
    schurGL v hg' = diag2 v (a 0) (a 1) * schurGL v hg := by
  apply Units.ext
  rw [Units.val_mul, schurGL_coe, schurGL_coe, diag2_coe, schurBlock_diagonal_mul v a hg]

private theorem charExt_units_mul (v : HeightOneSpectrum (𝓞 ℚ)) (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (u : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    TateLocal.charExt θ ((u : v.adicCompletion ℚ) * x) = ((θ u : ℂˣ) : ℂ) * TateLocal.charExt θ x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hux : (u : v.adicCompletion ℚ) * x ≠ 0 := mul_ne_zero u.ne_zero hx
    rw [TateLocal.charExt_of_ne_zero θ hux, TateLocal.charExt_of_ne_zero θ hx, ← Units.val_mul, ← map_mul]
    congr 2
    ext
    simp

private theorem mul_rpow_half_mul_sqrt_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x * y) ^ ((1 : ℝ) / 2) * Real.sqrt (x / y) = x := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow hx.le hy.le, Real.mul_rpow hx.le hy.le]
  have hx2 : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
    rw [← Real.rpow_add hx]
    norm_num
  have hy0 : y ^ ((1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
  field_simp
  linear_combination hx2

private theorem sectionFn_diagonal_mul (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {φ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ}
    (hφ : ∀ (d : GL (Fin 2) (v.adicCompletion ℚ)) (a₀ a₁ : (v.adicCompletion ℚ)ˣ),
      (d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
        Matrix.diagonal ![(a₀ : v.adicCompletion ℚ), (a₁ : v.adicCompletion ℚ)] →
      ∀ m, φ (d * m) = ((χ 0 a₀ : ℂˣ) : ℂ) * ((χ 1 a₁ : ℂˣ) : ℂ) *
        ((Real.sqrt (‖(a₀ : v.adicCompletion ℚ)‖ / ‖(a₁ : v.adicCompletion ℚ)‖) : ℝ) : ℂ) * φ m)
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    sectionFn v χ φ (diagonal3 v a * g) = torusChar3 v χ a * halfModulus3 v a * sectionFn v χ φ g := by
  unfold sectionFn
  by_cases hmem : g ∈ bigCell v
  · rw [Set.indicator_of_mem ((diagonal_mul_mem_bigCell_iff v a g).mpr hmem), Set.indicator_of_mem hmem]
    have hg : gl3Entry v g 2 2 ≠ 0 := hmem.1
    have hg' : gl3Entry v (diagonal3 v a * g) 2 2 ≠ 0 := by
      rw [gl3Entry_diagonal_mul]; exact mul_ne_zero (a 2).ne_zero hg
    rw [sectionValue_of_ne_zero v χ φ hg', sectionValue_of_ne_zero v χ φ hg, schurGL_diagonal_mul v a hg hg',
      hφ (diag2 v (a 0) (a 1)) (a 0) (a 1) (diag2_coe v (a 0) (a 1)), gl3Entry_diagonal_mul, charExt_units_mul,
      schurBlock_diagonal_mul v a hg, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_mul]
    rw [Real.mul_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)]
    have hc : ((((‖(a 0 : v.adicCompletion ℚ)‖ * ‖(a 1 : v.adicCompletion ℚ)‖) ^ ((1 : ℝ) / 2) : ℝ)) : ℂ) *
        ((Real.sqrt (‖(a 0 : v.adicCompletion ℚ)‖ / ‖(a 1 : v.adicCompletion ℚ)‖) : ℝ) : ℂ) =
        ((‖(a 0 : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul,
        mul_rpow_half_mul_sqrt_div (norm_pos_iff.mpr (a 0).ne_zero) (norm_pos_iff.mpr (a 1).ne_zero)]
    simp only [torusChar3, halfModulus3, Fin.prod_univ_three, mul_inv, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_div]
    linear_combination (((χ 0 (a 0) : ℂˣ) : ℂ) * ((χ 1 (a 1) : ℂˣ) : ℂ) * ((χ 2 (a 2) : ℂˣ) : ℂ) *
      TateLocal.charExt (χ 2) (gl3Entry v g 2 2) * ((‖gl3Entry v g 2 2‖ : ℝ) : ℂ)⁻¹ *
      ((‖(schurBlock v g).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * φ (schurGL v hg) *
      ((‖(a 2 : v.adicCompletion ℚ)‖ : ℝ) : ℂ)⁻¹) * hc
  · rw [Set.indicator_of_notMem (fun h => hmem ((diagonal_mul_mem_bigCell_iff v a g).mp h)),
      Set.indicator_of_notMem hmem, mul_zero]

private theorem exists_lower_entry_ne_zero_of_corner_eq_zero (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v}
    (hc : gl3Entry v g 2 2 = 0) : gl3Entry v g 2 0 ≠ 0 ∨ gl3Entry v g 2 1 ≠ 0 := by
  by_contra h
  push Not at h
  apply gl3Det_ne_zero v g
  simp [gl3Det_eq_bottom_expansion, h.1, h.2, hc]

private theorem eventually_sectionFn_eq_zero_of_corner (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (φ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) {g : LocalGL3 v}
    (i : Fin 2) (hn : gl3Entry v g 2 (Fin.castSucc i) ≠ 0) (hc : gl3Entry v g 2 2 = 0) :
    ∀ᶠ h in nhds g, sectionFn v χ φ h = sectionFn v χ φ g := by
  have hg : g ∉ bigCell v := fun hmem => hmem.1 hc
  filter_upwards [eventually_one_lt_valued_div v (continuous_gl3Entry v 2 (Fin.castSucc i)) (continuous_gl3Entry v 2 2)
    hn hc] with h hh
  have hh' : h ∉ bigCell v := fun hmem => by
    have h1 := hh hmem.1
    exact absurd (hmem.2 i) (not_le.mpr h1)
  rw [sectionFn, Set.indicator_of_notMem hh', Set.indicator_of_notMem hg]

private theorem continuousAt_schurBlock (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v}
    (hc : gl3Entry v g 2 2 ≠ 0) : ContinuousAt (schurBlock v) g := by
  have hE : ∀ i j : Fin 3, ContinuousAt (fun h : LocalGL3 v => gl3Entry v h i j) g :=
    fun i j => (continuous_gl3Entry v i j).continuousAt
  refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [schurBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one,
      Fin.isValue] <;>
    exact (hE _ _).sub (((hE _ _).mul (hE _ _)).div (hE 2 2) hc)

private theorem continuousAt_schurBlock_det (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v}
    (hc : gl3Entry v g 2 2 ≠ 0) : ContinuousAt (fun h => (schurBlock v h).det) g :=
  (continuous_id.matrix_det).continuousAt.comp (continuousAt_schurBlock v hc)

private theorem continuousAt_schurBlock_inv (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v}
    (hc : gl3Entry v g 2 2 ≠ 0) : ContinuousAt (fun h => (schurBlock v h)⁻¹) g := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact ((continuousAt_schurBlock_det v hc).inv₀ (schurBlock_det_ne_zero v hc)).smul
    ((continuous_id.matrix_adjugate).continuousAt.comp (continuousAt_schurBlock v hc))

private noncomputable def schurTotal (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    GL (Fin 2) (v.adicCompletion ℚ) := by
  classical exact if hg : gl3Entry v g 2 2 ≠ 0 then schurGL v hg else 1

private theorem schurTotal_eq (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v} (hg : gl3Entry v g 2 2 ≠ 0) :
    schurTotal v g = schurGL v hg := by
  unfold schurTotal
  rw [dif_pos hg]

private theorem schurTotal_val (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v} (hg : gl3Entry v g 2 2 ≠ 0) :
    ((schurTotal v g : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      schurBlock v g := by
  rw [schurTotal_eq v hg, schurGL_coe]

private theorem schurTotal_inv_val (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v} (hg : gl3Entry v g 2 2 ≠ 0) :
    (((schurTotal v g)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      (schurBlock v g)⁻¹ := by
  rw [Matrix.coe_units_inv, schurTotal_val v hg]

private theorem continuousAt_schurTotal (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v}
    (hc : gl3Entry v g 2 2 ≠ 0) : ContinuousAt (schurTotal v) g := by
  rw [Units.isInducing_embedProduct.continuousAt_iff]
  have hev : ∀ᶠ h in nhds g, gl3Entry v h 2 2 ≠ 0 := (continuous_gl3Entry v 2 2).continuousAt.eventually_ne hc
  have hexplicit : ContinuousAt (fun h : LocalGL3 v => (schurBlock v h, MulOpposite.op (schurBlock v h)⁻¹)) g :=
    (continuousAt_schurBlock v hc).prodMk
      (MulOpposite.continuous_op.continuousAt.comp (continuousAt_schurBlock_inv v hc))
  refine hexplicit.congr ?_
  filter_upwards [hev] with h hh
  simp only [Function.comp_apply, Units.embedProduct_apply, schurTotal_val v hh, schurTotal_inv_val v hh]

private theorem isLocallyConstant_sectionFn (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : IsLocallyConstant (χ 2)) {φ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ} (hφ : IsLocallyConstant φ) :
    IsLocallyConstant (sectionFn v χ φ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  by_cases hc : gl3Entry v g 2 2 = 0
  · rcases exists_lower_entry_ne_zero_of_corner_eq_zero v hc with h20 | h21
    · exact eventually_sectionFn_eq_zero_of_corner v χ φ 0 h20 hc
    · exact eventually_sectionFn_eq_zero_of_corner v χ φ 1 h21 hc
  have hcA : ContinuousAt (fun h : LocalGL3 v => gl3Entry v h 2 2) g := (continuous_gl3Entry v 2 2).continuousAt
  have hmem : ∀ᶠ h in nhds g, (h ∈ bigCell v ↔ g ∈ bigCell v) := by
    have hc' : ∀ᶠ h in nhds g, gl3Entry v h 2 2 ≠ 0 := hcA.eventually_ne hc
    have hr' : ∀ᶠ h in nhds g, ∀ i : Fin 2, (Valued.v (lowerRatio v h i) ≤ 1 ↔ Valued.v (lowerRatio v g i) ≤ 1) :=
      Filter.eventually_all.mpr fun i =>
        (((continuous_gl3Entry v 2 (Fin.castSucc i)).continuousAt.div hcA hc).eventually
          (eventually_mem_iff_of_isClopen v (isClopen_valued_le_one v) (lowerRatio v g i)))
    filter_upwards [hc', hr'] with h hch hrh
    simp only [bigCell, Set.mem_setOf_eq, hch, hc, ne_eq, not_false_eq_true, true_and]
    exact forall_congr' hrh
  have hval : ∀ᶠ h in nhds g, sectionValue v χ φ h = sectionValue v χ φ g := by
    have e1 : ∀ᶠ h in nhds g, gl3Entry v h 2 2 ≠ 0 := hcA.eventually_ne hc
    have e2 : ∀ᶠ h in nhds g,
        TateLocal.charExt (χ 2) (gl3Entry v h 2 2) = TateLocal.charExt (χ 2) (gl3Entry v g 2 2) :=
      hcA.eventually (eventually_charExt_eq v (χ 2) hχ hc)
    have e3 : ∀ᶠ h in nhds g, ‖gl3Entry v h 2 2‖ = ‖gl3Entry v g 2 2‖ := hcA.eventually (eventually_norm_eq v hc)
    have e4 : ∀ᶠ h in nhds g, ‖(schurBlock v h).det‖ = ‖(schurBlock v g).det‖ :=
      (continuousAt_schurBlock_det v hc).eventually (eventually_norm_eq v (schurBlock_det_ne_zero v hc))
    have e5 : ∀ᶠ h in nhds g, φ (schurTotal v h) = φ (schurTotal v g) :=
      (continuousAt_schurTotal v hc).eventually ((IsLocallyConstant.iff_eventually_eq _).mp hφ (schurTotal v g))
    filter_upwards [e1, e2, e3, e4, e5] with h h1 h2 h3 h4 h5
    rw [sectionValue_of_ne_zero v χ φ h1, sectionValue_of_ne_zero v χ φ hc, ← schurTotal_eq v h1,
      ← schurTotal_eq v hc, h2, h3, h4, h5]
  filter_upwards [hmem, hval] with h h1 h2
  by_cases hgS : g ∈ bigCell v
  · rw [sectionFn, Set.indicator_of_mem (h1.mpr hgS), Set.indicator_of_mem hgS, h2]
  · rw [sectionFn, Set.indicator_of_notMem (fun hh => hgS (h1.mp hh)), Set.indicator_of_notMem hgS]

private theorem restrictFn_add (v : HeightOneSpectrum (𝓞 ℚ)) (f g : LocalGL3 v → ℂ) :
    restrictFn v (f + g) = restrictFn v f + restrictFn v g := by
  funext m
  simp only [restrictFn, Pi.add_apply]
  ring

private theorem restrictFn_smul (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℂ) (f : LocalGL3 v → ℂ) :
    restrictFn v (a • f) = a • restrictFn v f := by
  funext m
  simp only [restrictFn, Pi.smul_apply, smul_eq_mul]
  ring

private theorem diagonal2_coe_pair (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    (diagonal2 v a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(a 0 : v.adicCompletion ℚ), (a 1 : v.adicCompletion ℚ)] := by
  rw [diagonal2_coe]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem eq_upperUnipotent2_of_entries (v : HeightOneSpectrum (𝓞 ℚ)) (u : GL (Fin 2) (v.adicCompletion ℚ))
    (h00 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 = 1)
    (h11 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1)
    (h10 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0) :
    u = upperUnipotent2 v ((u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) := by
  apply Units.ext
  rw [upperUnipotent2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h10]

private theorem eq_diagonal2_of_coe (v : HeightOneSpectrum (𝓞 ℚ)) (d : GL (Fin 2) (v.adicCompletion ℚ))
    (a₀ a₁ : (v.adicCompletion ℚ)ˣ)
    (hd : (d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(a₀ : v.adicCompletion ℚ), (a₁ : v.adicCompletion ℚ)]) :
    d = diagonal2 v ![a₀, a₁] := by
  apply Units.ext
  rw [hd, diagonal2_coe_pair]
  rfl

private theorem torusChar2_mul_halfModulus2_pair (v : HeightOneSpectrum (𝓞 ℚ)) (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (a₀ a₁ : (v.adicCompletion ℚ)ˣ) :
    torusChar2 v ![θ, θ] ![a₀, a₁] * halfModulus2 v ![a₀, a₁] =
      ((θ a₀ : ℂˣ) : ℂ) * ((θ a₁ : ℂˣ) : ℂ) *
        ((Real.sqrt (‖(a₀ : v.adicCompletion ℚ)‖ / ‖(a₁ : v.adicCompletion ℚ)‖) : ℝ) : ℂ) := by
  simp [torusChar2, halfModulus2, Fin.prod_univ_two]

private theorem restrictFn_mem (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v ![θ, θ, θ']) : restrictFn v f ∈ principalSeries2 v ![θ, θ] := by
  refine ⟨isLocallyConstant_restrictFn v ![θ, θ, θ'] hf, fun x m => ?_, fun a m => ?_⟩
  · exact restrictFn_unipotent_mul v ![θ, θ, θ'] hf (upperUnipotent2 v x) (by simp) (by simp) (by simp) m
  · rw [restrictFn_diagonal_mul v ![θ, θ, θ'] hf (diagonal2 v a) (a 0) (a 1) (diagonal2_coe_pair v a) m]
    simp only [torusChar2, halfModulus2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

private noncomputable def restrictLin (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) :
    ↥(principalSeries3 v ![θ, θ, θ']) →ₗ[ℂ] ↥(principalSeries2 v ![θ, θ]) where
  toFun f := ⟨restrictFn v f, restrictFn_mem v θ θ' f.2⟩
  map_add' f g := by
    ext m
    simp only [Submodule.coe_add, restrictFn_add, Pi.add_apply]
  map_smul' a f := by
    ext m
    simp only [Submodule.coe_smul, restrictFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

private theorem restrictLin_apply_coe (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (f : ↥(principalSeries3 v ![θ, θ, θ'])) :
    ((restrictLin v θ θ' f : ↥(principalSeries2 v ![θ, θ])) : LocalGL2 v → ℂ) = restrictFn v f := rfl

private theorem sectionFn_mem (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hlc : ∀ i, IsLocallyConstant (![θ, θ, θ'] i)) {φ : LocalGL2 v → ℂ} (hφ : φ ∈ principalSeries2 v ![θ, θ]) :
    sectionFn v ![θ, θ, θ'] φ ∈ principalSeries3 v ![θ, θ, θ'] := by
  refine ⟨isLocallyConstant_sectionFn v ![θ, θ, θ'] (hlc 2) hφ.1, fun x y z g => ?_, fun a g => ?_⟩
  · refine sectionFn_unipotent_mul v ![θ, θ, θ'] (fun u h00 h11 h10 m => ?_) x y z g
    rw [eq_upperUnipotent2_of_entries v u h00 h11 h10]
    exact hφ.2.1 _ m
  · refine sectionFn_diagonal_mul v ![θ, θ, θ'] (fun d a₀ a₁ hd m => ?_) a g
    rw [eq_diagonal2_of_coe v d a₀ a₁ hd, hφ.2.2 ![a₀, a₁] m, torusChar2_mul_halfModulus2_pair]
    simp

private theorem restrictLin_surjective (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hlc : ∀ i, IsLocallyConstant (![θ, θ, θ'] i)) : Function.Surjective (restrictLin v θ θ') := by
  intro φ
  refine ⟨⟨sectionFn v ![θ, θ, θ'] φ, sectionFn_mem v θ θ' hlc φ.2⟩, ?_⟩
  ext m
  exact restrictFn_sectionFn v ![θ, θ, θ'] φ m

private theorem leviNorm_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    leviNorm v m ≠ 0 := by
  unfold leviNorm
  exact_mod_cast (Real.rpow_pos_of_pos (det_norm_pos v m) _).ne'

private theorem iotaGL_bottom_entries (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    ((iotaGL m : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
      ((iotaGL m : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 := by
  constructor <;> simp [embedMat2]

private theorem corner_ne_zero_of_parabolic (v : HeightOneSpectrum (𝓞 ℚ)) {p : LocalGL3 v}
    (h20 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0) : gl3Entry v p 2 2 ≠ 0 := by
  intro h22
  apply gl3Det_ne_zero v p
  rw [gl3Det_eq_bottom_expansion]
  simp only [gl3Entry] at h22 ⊢
  rw [h20, h21, h22]
  ring

private theorem exists_apply_eq_mul_apply_iotaGL (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    {p : LocalGL3 v} (h20 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0) :
    ∃ (A : GL (Fin 2) (v.adicCompletion ℚ)) (s : ℂ), f p = s * f (iotaGL A) := by
  have hc : gl3Entry v p 2 2 ≠ 0 := corner_ne_zero_of_parabolic v h20 h21
  have hblock : ∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
      = ((schurGL v hc : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j := by
    intro i j
    rw [schurGL_coe]
    fin_cases i <;> fin_cases j <;> simp [schurBlock, gl3Entry, h20, h21]
  obtain ⟨y, z, hp⟩ := exists_radical_mul_of_block v p (schurGL v hc) (Units.mk0 _ hc) h20 h21 rfl hblock
  refine ⟨schurGL v hc, torusChar3 v χ ![1, 1, Units.mk0 _ hc] * halfModulus3 v ![1, 1, Units.mk0 _ hc], ?_⟩
  calc f p = f (upperUnipotent3 0 y z * (iotaGL (schurGL v hc) * diagonal3 v ![1, 1, Units.mk0 _ hc])) := by
        rw [← hp]
    _ = _ := by
        rw [apply_upperUnipotent3_mul_of_mem_principalSeries3 hf, iotaGL_mul_center,
          apply_diagonal3_mul_of_mem_principalSeries3 hf]

private theorem restrictLin_eq_zero_iff (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (f : ↥(principalSeries3 v ![θ, θ, θ'])) :
    restrictLin v θ θ' f = 0 ↔
      ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
        (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → (f : LocalGL3 v → ℂ) p = 0 := by
  constructor
  · intro h p h20 h21
    have hι : ∀ m : GL (Fin 2) (v.adicCompletion ℚ), (f : LocalGL3 v → ℂ) (iotaGL m) = 0 := by
      intro m
      have hm : restrictFn v f m = 0 := by
        have h' := congrArg (fun ψ : ↥(principalSeries2 v ![θ, θ]) => (ψ : LocalGL2 v → ℂ) m) h
        simpa [restrictLin_apply_coe] using h'
      unfold restrictFn at hm
      exact (mul_eq_zero.mp hm).resolve_left (leviNorm_ne_zero v m)
    obtain ⟨A, s, hs⟩ := exists_apply_eq_mul_apply_iotaGL v ![θ, θ, θ'] f.2 h20 h21
    rw [hs, hι A, mul_zero]
  · intro h
    ext m
    rw [restrictLin_apply_coe, Submodule.coe_zero, Pi.zero_apply, restrictFn,
      h (iotaGL m) (iotaGL_bottom_entries v m).1 (iotaGL_bottom_entries v m).2, mul_zero]

private theorem principalSeries2Rep_apply_coe (v : HeightOneSpectrum (𝓞 ℚ)) (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (A : LocalGL2 v) (φ : ↥(principalSeries2 v ![θ, θ])) (m : LocalGL2 v) :
    ((principalSeries2Rep (v := v) ![θ, θ] A φ : ↥(principalSeries2 v ![θ, θ])) : LocalGL2 v → ℂ) m =
      (φ : LocalGL2 v → ℂ) (m * A) := rfl

private theorem vec3_apply_two (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) :
    ![θ, θ, θ'] 2 = θ' := rfl

private theorem restrictLin_rightTranslate (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ)
    (f : ↥(principalSeries3 v ![θ, θ, θ']))
    (h20 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0)
    (h22 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ))
    (hblock : ∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) :
    restrictLin v θ θ' ⟨gl3AmbientRightTranslate (R := ℂ) p f, rightTranslate_mem_principalSeries3 f.2 p⟩
      = ((((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2)) /
          ‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) •
        (((θ' c : ℂˣ) : ℂ) • (principalSeries2Rep (v := v) ![θ, θ]) A (restrictLin v θ θ' f))) := by
  ext m
  rw [restrictLin_apply_coe, Submodule.coe_smul, Pi.smul_apply, Submodule.coe_smul, Pi.smul_apply,
    principalSeries2Rep_apply_coe, restrictLin_apply_coe,
    restrictFn_rightTranslate v ![θ, θ, θ'] f.2 p A c h20 h21 h22 hblock m, smul_eq_mul, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_inv, vec3_apply_two]
  ring

private theorem exists_surjective_leviRestriction_principalSeries3
    (v : HeightOneSpectrum (𝓞 ℚ))
    (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hlc : ∀ i, IsLocallyConstant (![θ, θ, θ'] i)) :
    ∃ Ψ : ↥(principalSeries3 v ![θ, θ, θ']) →ₗ[ℂ] ↥(principalSeries2 v ![θ, θ]), Function.Surjective Ψ ∧
        (∀ f : ↥(principalSeries3 v ![θ, θ, θ']), Ψ f = 0 ↔
          ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
            (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → (f : LocalGL3 v → ℂ) p = 0) ∧
        ∀ (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ)
          (f : ↥(principalSeries3 v ![θ, θ, θ'])),
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ) →
          (∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
            = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) →
          Ψ ⟨gl3AmbientRightTranslate (R := ℂ) p f, rightTranslate_mem_principalSeries3 f.2 p⟩
            = ((((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2)) /
              ‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) • (((θ' c : ℂˣ) : ℂ) •
                (principalSeries2Rep (v := v) ![θ, θ]) A (Ψ f))) := by
  refine ⟨restrictLin v θ θ', restrictLin_surjective v θ θ' hlc, fun f => restrictLin_eq_zero_iff v θ θ' f, ?_⟩
  intro p A c f h20 h21 h22 hblock
  exact restrictLin_rightTranslate v θ θ' p A c f h20 h21 h22 hblock

end LanglandsTunnell.CubicInduction.LeviRestriction

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace PadicTransport
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable abbrev primeUnder : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)

private scoped instance fact_prime_primeUnder : Fact (primeUnder v).Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

private theorem asIdeal_eq_span_primeUnder : v.asIdeal = Ideal.span {(primeUnder v : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator v
  have hc := v.asIdeal.comap_map_of_bijective (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))
    (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).bijective
  rw [← h, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton, map_natCast] at hc
  exact hc.symm

private theorem absNorm_asIdeal : Ideal.absNorm v.asIdeal = primeUnder v := by
  rw [asIdeal_eq_span_primeUnder, Ideal.absNorm_span_singleton]
  have h1 : ((primeUnder v : 𝓞 ℚ)) = algebraMap ℤ (𝓞 ℚ) (primeUnder v : ℤ) := by simp
  rw [h1, Algebra.norm_algebraMap, RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast]

private theorem norm_le_one_iff_mem (x : v.adicCompletion ℚ) : ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers ℚ := by
  rw [FinitePlace.norm_def, HeightOneSpectrum.mem_adicCompletionIntegers, ← NNReal.coe_one, NNReal.coe_le_coe,
    WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)]

private theorem exists_norm_eq_zpow {x : v.adicCompletion ℚ} (hx : x ≠ 0) : ∃ m : ℤ, ‖x‖ = (primeUnder v : ℝ) ^ m := by
  have hv : Valued.v x ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv), ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow]
  simp [absNorm_asIdeal]

private theorem valued_primeUnder : Valued.v (primeUnder v : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  have hp0 : (primeUnder v : 𝓞 ℚ) ≠ 0 := by exact_mod_cast (fact_prime_primeUnder v).out.ne_zero
  have h1 : (primeUnder v : v.adicCompletion ℚ) = algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (primeUnder v : 𝓞 ℚ) :=
    (map_natCast _ _).symm
  have h2 : Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (primeUnder v : 𝓞 ℚ)) =
      v.intValuation (primeUnder v : 𝓞 ℚ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation v (primeUnder v : 𝓞 ℚ)).trans
      (v.valuation_of_algebraMap (K := ℚ) (primeUnder v : 𝓞 ℚ))
  rw [h1, h2, HeightOneSpectrum.intValuation_singleton _ hp0 (asIdeal_eq_span_primeUnder v)]

private theorem norm_primeUnder : ‖(primeUnder v : v.adicCompletion ℚ)‖ = (primeUnder v : ℝ)⁻¹ := by
  have hne : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [FinitePlace.norm_def, valued_primeUnder, WithZeroMulInt.toNNReal_neg_apply _ hne, NNReal.coe_zpow]
  have h2 : Multiplicative.toAdd (WithZero.unzero hne) = -1 := rfl
  rw [h2, zpow_neg, zpow_one]
  simp [absNorm_asIdeal]

private theorem norm_padicEquiv_le_one_iff (x : v.adicCompletion ℚ) :
    ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  have hb := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v
  rw [norm_le_one_iff_mem, ← PadicInt.mem_subring_iff]
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := hb.surjOn h
    rwa [← (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective hyx]
  · exact fun h => hb.mapsTo h

private theorem padicEquiv_primeUnder :
    Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (primeUnder v : v.adicCompletion ℚ) =
      (primeUnder v : ℚ_[primeUnder v]) :=
  map_natCast _ _

private theorem norm_padicEquiv (x : v.adicCompletion ℚ) :
    ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hex : Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x ≠ 0 := fun h =>
    hx (by simpa using congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm h)
  have hp1 : (1 : ℝ) < primeUnder v := by exact_mod_cast (fact_prime_primeUnder v).out.one_lt
  have hp0 : (0 : ℝ) < primeUnder v := zero_lt_one.trans hp1

  have hscale : ∀ (m : ℤ) (y : v.adicCompletion ℚ), ‖y * (primeUnder v : v.adicCompletion ℚ) ^ m‖ =
      ‖y‖ * ((primeUnder v : ℝ) ^ m)⁻¹ := by
    intro m y
    rw [norm_mul, norm_zpow, norm_primeUnder, inv_zpow]
  have hscale' : ∀ (m : ℤ) (y : v.adicCompletion ℚ),
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (y * (primeUnder v : v.adicCompletion ℚ) ^ m)‖ =
        ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v y‖ * ((primeUnder v : ℝ) ^ m)⁻¹ := by
    intro m y
    rw [map_mul, map_zpow₀, padicEquiv_primeUnder, norm_mul, norm_zpow, Padic.norm_p, inv_zpow]
  obtain ⟨m, hm⟩ := exists_norm_eq_zpow v hx
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x‖ = (primeUnder v : ℝ) ^ n :=
    ⟨-(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x).valuation, Padic.norm_eq_zpow_neg_valuation hex⟩
  have hpm : (0 : ℝ) < (primeUnder v : ℝ) ^ m := zpow_pos hp0 m
  have hpn : (0 : ℝ) < (primeUnder v : ℝ) ^ n := zpow_pos hp0 n
  apply le_antisymm
  ·
    have h1 : ‖x * (primeUnder v : v.adicCompletion ℚ) ^ m‖ ≤ 1 := by
      rw [hscale, hm, mul_inv_cancel₀ hpm.ne']
    have h2 := (norm_padicEquiv_le_one_iff v _).mpr h1
    rw [hscale', hn] at h2
    rw [hm, hn]
    rwa [← div_eq_mul_inv, div_le_one hpm] at h2
  ·
    have h1 :
        ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (x * (primeUnder v : v.adicCompletion ℚ) ^ n)‖ ≤ 1 := by
      rw [hscale', hn, mul_inv_cancel₀ hpn.ne']
    have h2 := (norm_padicEquiv_le_one_iff v _).mp h1
    rw [hscale, hm] at h2
    rw [hm, hn]
    rwa [← div_eq_mul_inv, div_le_one hpn] at h2

end LanglandsTunnell.CubicInduction.PadicTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace PadicTransport
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private def glEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) : GL (Fin 2) A ≃* GL (Fin 2) B where
  toFun := Matrix.GeneralLinearGroup.map e.toRingHom
  invFun := Matrix.GeneralLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' g h := map_mul _ g h

private theorem glEquiv_apply {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (g : GL (Fin 2) A) (i j : Fin 2) :
    (glEquiv e g : Matrix (Fin 2) (Fin 2) B) i j = e ((g : Matrix (Fin 2) (Fin 2) A) i j) :=
  rfl

private theorem glEquiv_symm_apply {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (g : GL (Fin 2) B)
    (i j : Fin 2) :
    ((glEquiv e).symm g : Matrix (Fin 2) (Fin 2) A) i j = e.symm ((g : Matrix (Fin 2) (Fin 2) B) i j) :=
  rfl

private theorem continuous_glMap {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ (continuous_id.matrix_map hf)

private theorem isLocallyConstant_comp_glMap {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f)
    {φ : GL (Fin 2) B → ℂ} (hφ : IsLocallyConstant φ) :
    IsLocallyConstant (φ ∘ Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  hφ.comp_continuous (continuous_glMap f hf)

end LanglandsTunnell.CubicInduction.PadicTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace PadicTransport
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def ratRingEquiv : v.adicCompletion ℚ ≃+* ℚ_[primeUnder v] :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv

private theorem ratRingEquiv_apply (x : v.adicCompletion ℚ) :
    ratRingEquiv v x = Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x :=
  rfl

private theorem continuous_ratRingEquiv : Continuous (ratRingEquiv v) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).continuous

private theorem continuous_ratRingEquiv_symm : Continuous (ratRingEquiv v).symm :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous

private theorem norm_ratRingEquiv (x : v.adicCompletion ℚ) : ‖ratRingEquiv v x‖ = ‖x‖ :=
  norm_padicEquiv v x

private theorem norm_ratRingEquiv_symm (y : ℚ_[primeUnder v]) : ‖(ratRingEquiv v).symm y‖ = ‖y‖ := by
  rw [← norm_ratRingEquiv v ((ratRingEquiv v).symm y), RingEquiv.apply_symm_apply]

private theorem ratRingEquiv_toMonoidHom_apply (x : v.adicCompletion ℚ) :
    (ratRingEquiv v).toMonoidHom x = ratRingEquiv v x := rfl

private theorem ratRingEquiv_symm_toMonoidHom_apply (y : ℚ_[primeUnder v]) :
    (ratRingEquiv v).symm.toMonoidHom y = (ratRingEquiv v).symm y := rfl

private noncomputable def charTransport (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) : ℚ_[primeUnder v]ˣ →* ℂˣ :=
  θ.comp (Units.map (ratRingEquiv v).symm.toMonoidHom)

private theorem charTransport_apply (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℚ_[primeUnder v]ˣ) :
    charTransport v θ a = θ (Units.map (ratRingEquiv v).symm.toMonoidHom a) :=
  rfl

private noncomputable def glTransport : LocalGL2 v ≃* GL (Fin 2) ℚ_[primeUnder v] :=
  glEquiv (ratRingEquiv v)

private theorem continuous_glTransport : Continuous (glTransport v) :=
  continuous_glMap (ratRingEquiv v).toRingHom (continuous_ratRingEquiv v)

private theorem continuous_glTransport_symm : Continuous (glTransport v).symm :=
  continuous_glMap (ratRingEquiv v).symm.toRingHom (continuous_ratRingEquiv_symm v)

private noncomputable def glTransportHomeomorph : LocalGL2 v ≃ₜ GL (Fin 2) ℚ_[primeUnder v] where
  toEquiv := (glTransport v).toEquiv
  continuous_toFun := continuous_glTransport v
  continuous_invFun := continuous_glTransport_symm v

private theorem isOpenMap_glTransport : IsOpenMap (glTransport v) :=
  (glTransportHomeomorph v).isOpenMap

private theorem glTransport_upperUnipotent2 (x : v.adicCompletion ℚ) :
    glTransport v (upperUnipotent2 v x) = LocalNewvector.borelElem (primeUnder v) 1 1 (ratRingEquiv v x) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [LocalNewvector.coe_borelElem]
  show ratRingEquiv v ((upperUnipotent2 v x : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) = _
  rw [upperUnipotent2_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem glTransport_diagonal2 (a : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    glTransport v (diagonal2 v a) = LocalNewvector.borelElem (primeUnder v)
      (Units.map (ratRingEquiv v).toMonoidHom (a 0)) (Units.map (ratRingEquiv v).toMonoidHom (a 1)) 0 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [LocalNewvector.coe_borelElem]
  show ratRingEquiv v ((diagonal2 v a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) = _
  rw [diagonal2_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem glTransport_symm_borelElem (a₁ a₂ : ℚ_[primeUnder v]ˣ) (x : ℚ_[primeUnder v]) :
    (glTransport v).symm (LocalNewvector.borelElem (primeUnder v) a₁ a₂ x) =
      diagonal2 v ![Units.map (ratRingEquiv v).symm.toMonoidHom a₁, Units.map (ratRingEquiv v).symm.toMonoidHom a₂] *
        upperUnipotent2 v ((ratRingEquiv v).symm ((a₁ : ℚ_[primeUnder v])⁻¹ * x)) := by
  apply (glTransport v).injective
  rw [MulEquiv.apply_symm_apply, map_mul, glTransport_diagonal2, glTransport_upperUnipotent2,
    LocalNewvector.borelElem_mul]
  have h1 : Units.map (ratRingEquiv v).toMonoidHom (Units.map (ratRingEquiv v).symm.toMonoidHom a₁) = a₁ :=
    Units.ext ((ratRingEquiv v).apply_symm_apply _)
  have h2 : Units.map (ratRingEquiv v).toMonoidHom (Units.map (ratRingEquiv v).symm.toMonoidHom a₂) = a₂ :=
    Units.ext ((ratRingEquiv v).apply_symm_apply _)
  have h3 : ratRingEquiv v ((ratRingEquiv v).symm ((a₁ : ℚ_[primeUnder v])⁻¹ * x)) = (a₁ : ℚ_[primeUnder v])⁻¹ * x :=
    (ratRingEquiv v).apply_symm_apply _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h1, h2, h3, mul_one, zero_mul, add_zero]
  congr 1
  rw [mul_inv_cancel_left₀ a₁.ne_zero]

private theorem torusChar2_transport (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₁ a₂ : ℚ_[primeUnder v]ˣ) :
    torusChar2 v χ ![Units.map (ratRingEquiv v).symm.toMonoidHom a₁, Units.map (ratRingEquiv v).symm.toMonoidHom a₂] =
      ((charTransport v (χ 0) a₁ : ℂˣ) : ℂ) * ((charTransport v (χ 1) a₂ : ℂˣ) : ℂ) := by
  simp only [torusChar2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, charTransport_apply]

private theorem halfModulus2_transport (a₁ a₂ : ℚ_[primeUnder v]ˣ) :
    halfModulus2 v ![Units.map (ratRingEquiv v).symm.toMonoidHom a₁, Units.map (ratRingEquiv v).symm.toMonoidHom a₂] =
      LocalNewvector.halfModulus (primeUnder v) a₁ a₂ := by
  simp only [halfModulus2, LocalNewvector.halfModulus, Matrix.cons_val_zero, Matrix.cons_val_one, Units.coe_map,
    ratRingEquiv_symm_toMonoidHom_apply, norm_ratRingEquiv_symm]

private theorem torusChar2_eq_charTransport (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (a : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    torusChar2 v χ a = ((charTransport v (χ 0) (Units.map (ratRingEquiv v).toMonoidHom (a 0)) : ℂˣ) : ℂ) *
      ((charTransport v (χ 1) (Units.map (ratRingEquiv v).toMonoidHom (a 1)) : ℂˣ) : ℂ) := by
  have h : ∀ i, Units.map (ratRingEquiv v).symm.toMonoidHom (Units.map (ratRingEquiv v).toMonoidHom (a i)) = a i :=
    fun i => Units.ext ((ratRingEquiv v).symm_apply_apply _)
  simp only [torusChar2, Fin.prod_univ_two, charTransport_apply, h]

private theorem halfModulus2_eq_halfModulus (a : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    halfModulus2 v a = LocalNewvector.halfModulus (primeUnder v) (Units.map (ratRingEquiv v).toMonoidHom (a 0))
      (Units.map (ratRingEquiv v).toMonoidHom (a 1)) := by
  simp only [halfModulus2, LocalNewvector.halfModulus, Units.coe_map, ratRingEquiv_toMonoidHom_apply,
    norm_ratRingEquiv]

private theorem comp_glTransport_symm_mem (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL2 v → ℂ}
    (hf : f ∈ principalSeries2 v χ) :
    f ∘ (glTransport v).symm ∈
      LocalNewvector.principalSeries (primeUnder v) (charTransport v (χ 0)) (charTransport v (χ 1)) := by
  obtain ⟨hlc, hN, hT⟩ := mem_principalSeries2_iff.mp hf
  refine (LocalNewvector.mem_principalSeries_iff (primeUnder v)).mpr ⟨?_, fun a₁ a₂ x g => ?_⟩
  · exact hlc.comp_continuous (continuous_glTransport_symm v)
  · show f ((glTransport v).symm (LocalNewvector.borelElem (primeUnder v) a₁ a₂ x * g)) =
      _ * f ((glTransport v).symm g)
    rw [map_mul, glTransport_symm_borelElem, mul_assoc, hT, hN, torusChar2_transport, halfModulus2_transport]

private theorem comp_glTransport_mem (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {F : GL (Fin 2) ℚ_[primeUnder v] → ℂ}
    (hF : F ∈ LocalNewvector.principalSeries (primeUnder v) (charTransport v (χ 0)) (charTransport v (χ 1))) :
    F ∘ glTransport v ∈ principalSeries2 v χ := by
  obtain ⟨hlc, hB⟩ := (LocalNewvector.mem_principalSeries_iff (primeUnder v)).mp hF
  refine mem_principalSeries2_iff.mpr ⟨?_, fun x g => ?_, fun a g => ?_⟩
  · exact hlc.comp_continuous (continuous_glTransport v)
  · show F (glTransport v (upperUnipotent2 v x * g)) = F (glTransport v g)
    rw [map_mul, glTransport_upperUnipotent2, hB]
    simp [LocalNewvector.halfModulus]
  · show F (glTransport v (diagonal2 v a * g)) = _ * F (glTransport v g)
    rw [map_mul, glTransport_diagonal2, hB, torusChar2_eq_charTransport, halfModulus2_eq_halfModulus]

private noncomputable def carrierTransport (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    ↥(principalSeries2 v χ) ≃ₗ[ℂ]
      LocalNewvector.PSCarrier (primeUnder v) (charTransport v (χ 0)) (charTransport v (χ 1)) where
  toFun f := LocalNewvector.PSCarrier.mk _ _ _ ⟨(f : LocalGL2 v → ℂ) ∘ (glTransport v).symm,
    comp_glTransport_symm_mem v χ f.2⟩
  invFun F := ⟨LocalNewvector.PSCarrier.toFn _ _ _ F ∘ glTransport v,
    comp_glTransport_mem v χ (LocalNewvector.PSCarrier.toFn_mem _ _ _ F)⟩
  map_add' _ _ := LocalNewvector.PSCarrier.ext _ _ _ fun _ => rfl
  map_smul' _ _ := LocalNewvector.PSCarrier.ext _ _ _ fun _ => rfl
  left_inv f := Subtype.ext (funext fun g => congrArg (f : LocalGL2 v → ℂ) ((glTransport v).symm_apply_apply g))
  right_inv F := LocalNewvector.PSCarrier.ext _ _ _ fun y =>
    congrArg (LocalNewvector.PSCarrier.toFn _ _ _ F) ((glTransport v).apply_symm_apply y)

private theorem toFn_carrierTransport (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (f : ↥(principalSeries2 v χ))
    (y : GL (Fin 2) ℚ_[primeUnder v]) :
    LocalNewvector.PSCarrier.toFn _ _ _ (carrierTransport v χ f) y = (f : LocalGL2 v → ℂ) ((glTransport v).symm y) :=
  rfl

private theorem carrierTransport_principalSeries2Rep (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL2 v)
    (f : ↥(principalSeries2 v χ)) :
    carrierTransport v χ (principalSeries2Rep χ g f) = glTransport v g • carrierTransport v χ f := by
  refine LocalNewvector.PSCarrier.ext _ _ _ fun y => ?_
  rw [LocalNewvector.PSCarrier.toFn_smul, toFn_carrierTransport, toFn_carrierTransport, map_mul,
    MulEquiv.symm_apply_apply]
  rfl

end LanglandsTunnell.CubicInduction.PadicTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace PadicTransport
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isIrreducibleRep_of_isIrreducibleGLRep (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (h : LocalNewvector.IsIrreducibleGLRep (primeUnder v)
      (LocalNewvector.PSCarrier (primeUnder v) (charTransport v (χ 0)) (charTransport v (χ 1)))) :
    FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep (principalSeries2Rep χ) := by
  obtain ⟨⟨F, hF⟩, hW⟩ := h
  refine ⟨⟨(carrierTransport v χ).symm F, fun h0 => hF ?_⟩, fun W hWinv => ?_⟩
  · rw [← (carrierTransport v χ).apply_symm_apply F, h0, map_zero]
  · have hmap : ∀ (g' : GL (Fin 2) ℚ_[primeUnder v]) (F : LocalNewvector.PSCarrier (primeUnder v)
        (charTransport v (χ 0)) (charTransport v (χ 1))), F ∈ W.map (carrierTransport v χ).toLinearMap →
        g' • F ∈ W.map (carrierTransport v χ).toLinearMap := by
      intro g' F hF'
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hF'
      refine Submodule.mem_map.mpr ⟨principalSeries2Rep χ ((glTransport v).symm g') f, hWinv _ _ hf, ?_⟩
      rw [LinearEquiv.coe_toLinearMap, carrierTransport_principalSeries2Rep, MulEquiv.apply_symm_apply]
    have hinj : Function.Injective (Submodule.map (carrierTransport v χ).toLinearMap) :=
      Submodule.map_injective_of_injective (carrierTransport v χ).injective
    rcases hW _ hmap with hbot | htop
    · left
      apply hinj
      rw [hbot, Submodule.map_bot]
    · right
      apply hinj
      rw [htop, Submodule.map_top, LinearEquiv.range]

private theorem isLocallyConstant_det_char (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hθ : IsLocallyConstant θ) :
    IsLocallyConstant fun g : LocalGL2 v => ((θ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : LocalGL2 v → (v.adicCompletion ℚ)ˣ) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩
  exact (IsLocallyConstant.comp_continuous hθ hdet).comp fun u : ℂˣ => (u : ℂ)

private noncomputable def twistFn2 (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (f : LocalGL2 v → ℂ) : LocalGL2 v → ℂ :=
  fun g => ((θ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * f g

private noncomputable def untwistFn2 (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (f : LocalGL2 v → ℂ) : LocalGL2 v → ℂ :=
  fun g => ((θ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * f g

private theorem det_upperUnipotent2_mul (x : v.adicCompletion ℚ) (g : LocalGL2 v) :
    Matrix.GeneralLinearGroup.det (upperUnipotent2 v x * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul]
  have h : Matrix.GeneralLinearGroup.det (upperUnipotent2 v x) = 1 :=
    Units.ext (by simp [Matrix.det_fin_two])
  rw [h, one_mul]

private theorem det_diagonal2 (a : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    Matrix.GeneralLinearGroup.det (diagonal2 v a) = a 0 * a 1 :=
  Units.ext (by simp)

private theorem twistFn2_mem (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hθ : IsLocallyConstant θ) {f : LocalGL2 v → ℂ}
    (hf : f ∈ principalSeries2 v ![θ, θ]) : twistFn2 v θ f ∈ principalSeries2 v ![1, 1] := by
  obtain ⟨hlc, hN, hT⟩ := mem_principalSeries2_iff.mp hf
  refine mem_principalSeries2_iff.mpr ⟨?_, fun x g => ?_, fun a g => ?_⟩
  · exact ((isLocallyConstant_det_char v θ hθ).comp fun z : ℂ => z⁻¹).mul hlc
  · simp only [twistFn2, det_upperUnipotent2_mul, hN]
  · simp only [twistFn2, map_mul, det_diagonal2, hT, torusChar2, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul]
    have h0 : ((θ (a 0) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have h1 : ((θ (a 1) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hd : ((θ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp

private theorem untwistFn2_mem (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hθ : IsLocallyConstant θ) {f : LocalGL2 v → ℂ}
    (hf : f ∈ principalSeries2 v ![1, 1]) : untwistFn2 v θ f ∈ principalSeries2 v ![θ, θ] := by
  obtain ⟨hlc, hN, hT⟩ := mem_principalSeries2_iff.mp hf
  refine mem_principalSeries2_iff.mpr ⟨?_, fun x g => ?_, fun a g => ?_⟩
  · exact (isLocallyConstant_det_char v θ hθ).mul hlc
  · simp only [untwistFn2, det_upperUnipotent2_mul, hN]
  · simp only [untwistFn2, map_mul, det_diagonal2, hT, torusChar2, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul]
    ring

private noncomputable def twistEquiv2 (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hθ : IsLocallyConstant θ) :
    ↥(principalSeries2 v ![θ, θ]) ≃ₗ[ℂ] ↥(principalSeries2 v ![1, 1]) where
  toFun f := ⟨twistFn2 v θ f, twistFn2_mem v θ hθ f.2⟩
  invFun f := ⟨untwistFn2 v θ f, untwistFn2_mem v θ hθ f.2⟩
  map_add' _ _ := Subtype.ext (funext fun _ => mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => mul_left_comm _ _ _)
  left_inv _ := Subtype.ext (funext fun _ => mul_inv_cancel_left₀ (Units.ne_zero _) _)
  right_inv _ := Subtype.ext (funext fun _ => inv_mul_cancel_left₀ (Units.ne_zero _) _)

private theorem twistEquiv2_principalSeries2Rep (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hθ : IsLocallyConstant θ)
    (h : LocalGL2 v) (f : ↥(principalSeries2 v ![θ, θ])) :
    twistEquiv2 v θ hθ (principalSeries2Rep ![θ, θ] h f) =
      ((θ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) • principalSeries2Rep ![1, 1] h (twistEquiv2 v θ hθ f) := by
  refine Subtype.ext (funext fun g => ?_)
  show ((θ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * (f : LocalGL2 v → ℂ) (g * h) =
    ((θ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
      (((θ (Matrix.GeneralLinearGroup.det (g * h)) : ℂˣ) : ℂ)⁻¹ * (f : LocalGL2 v → ℂ) (g * h))
  have hg : ((θ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hh : ((θ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [map_mul, map_mul, Units.val_mul]
  field_simp

private theorem isIrreducibleRep_of_twist (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hθ : IsLocallyConstant θ)
    (h : FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep (principalSeries2Rep (v := v) ![1, 1])) :
    FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep (principalSeries2Rep (v := v) ![θ, θ]) := by
  obtain ⟨⟨F, hF⟩, hW⟩ := h
  refine ⟨⟨(twistEquiv2 v θ hθ).symm F, fun h0 => hF ?_⟩, fun W hWinv => ?_⟩
  · rw [← (twistEquiv2 v θ hθ).apply_symm_apply F, h0, map_zero]
  · have hmap : ∀ (g : LocalGL2 v) (F : ↥(principalSeries2 v ![1, 1])),
        F ∈ W.map (twistEquiv2 v θ hθ).toLinearMap →
          principalSeries2Rep ![1, 1] g F ∈ W.map (twistEquiv2 v θ hθ).toLinearMap := by
      intro g F hF'
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hF'
      refine Submodule.mem_map.mpr
        ⟨((θ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • principalSeries2Rep ![θ, θ] g f,
          W.smul_mem _ (hWinv _ _ hf), ?_⟩
      rw [LinearEquiv.coe_toLinearMap, map_smul, twistEquiv2_principalSeries2Rep, smul_smul,
        inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    have hinj : Function.Injective (Submodule.map (twistEquiv2 v θ hθ).toLinearMap) :=
      Submodule.map_injective_of_injective (twistEquiv2 v θ hθ).injective
    rcases hW _ hmap with hbot | htop
    · left
      apply hinj
      rw [hbot, Submodule.map_bot]
    · right
      apply hinj
      rw [htop, Submodule.map_top, LinearEquiv.range]

private theorem charTransport_one : charTransport v (1 : (v.adicCompletion ℚ)ˣ →* ℂˣ) = 1 :=
  MonoidHom.ext fun _ => rfl

private theorem isIrreducibleRep_principalSeries2Rep_pair (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hlc : ∀ i, IsLocallyConstant (![θ, θ, θ'] i)) :
    FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep (principalSeries2Rep (v := v) ![θ, θ]) := by
  have hθ : IsLocallyConstant θ := by simpa using hlc 0
  refine isIrreducibleRep_of_twist v θ hθ (isIrreducibleRep_of_isIrreducibleGLRep v ![1, 1] ?_)
  have h1 : charTransport v ((![1, 1] : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) 0) = 1 := charTransport_one v
  have h2 : charTransport v ((![1, 1] : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) 1) = 1 := charTransport_one v
  rw [h1, h2]
  refine LocalNewvector.PSCarrier.isIrreducibleGLRep_of_hasCharConductor_of_ratio (primeUnder v)
    (LocalNewvector.hasCharConductor_one_zero (primeUnder v)) (LocalNewvector.hasCharConductor_one_zero (primeUnder v))
    fun _ => ⟨?_, ?_⟩
  · intro h
    have h' : (primeUnder v : ℂ) = 1 := by simpa using h.symm
    exact (fact_prime_primeUnder v).out.one_lt.ne' (by exact_mod_cast h')
  · intro h
    have h' : (primeUnder v : ℂ) = 1 := by simpa using h.symm
    exact (fact_prime_primeUnder v).out.one_lt.ne' (by exact_mod_cast h')

end LanglandsTunnell.CubicInduction.PadicTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace FixedVectorTransport
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem apply_mem_fixedSubmodule_map_of_mem_fixedVectors
    {G : Type*} [Group G] {G' : Type*} [Group G'] {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [DistribMulAction G' W] [SMulCommClass G' ℂ W]
    (π : G →* Module.End ℂ V) (φ : G ≃* G') (e : V ≃ₗ[ℂ] W)
    (he : ∀ (g : G) (x : V), e (π g x) = φ g • e x) (K : Subgroup G) {x : V}
    (hx : x ∈ FLT.SmoothAdmissibleSchurCommutant.fixedVectors π K) :
    e x ∈ LocalNewvector.fixedSubmodule (K.map φ.toMonoidHom) W := by
  rw [LocalNewvector.mem_fixedSubmodule_iff]
  intro g' hg'
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg'
  rw [MulEquiv.coe_toMonoidHom, ← he, (FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors π).mp hx k hk]

private theorem finiteDimensional_fixedVectors_of_equiv
    {G : Type*} [Group G] {G' : Type*} [Group G'] {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [DistribMulAction G' W] [SMulCommClass G' ℂ W]
    (π : G →* Module.End ℂ V) (φ : G ≃* G') (e : V ≃ₗ[ℂ] W)
    (he : ∀ (g : G) (x : V), e (π g x) = φ g • e x) (K : Subgroup G)
    [FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (K.map φ.toMonoidHom) W)] :
    FiniteDimensional ℂ ↥(FLT.SmoothAdmissibleSchurCommutant.fixedVectors π K) := by
  refine FiniteDimensional.of_injective
    (e.toLinearMap.restrict fun x hx =>
      apply_mem_fixedSubmodule_map_of_mem_fixedVectors π φ e he K hx) ?_
  intro x y hxy
  have h : e x = e y := congrArg Subtype.val hxy
  exact Subtype.ext (e.injective h)

private theorem isOpen_coe_map_of_isOpenMap
    {G : Type*} [Group G] [TopologicalSpace G] {G' : Type*} [Group G'] [TopologicalSpace G']
    (φ : G ≃* G') (hφ : IsOpenMap φ) {K : Subgroup G} (hK : IsOpen (K : Set G)) :
    IsOpen ((K.map φ.toMonoidHom : Subgroup G') : Set G') := by
  rw [Subgroup.coe_map, MulEquiv.coe_toMonoidHom]
  exact hφ _ hK

end LanglandsTunnell.CubicInduction.FixedVectorTransport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace CellSectionLevel
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction"

section Level

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl2Entry_mul_one_zero (g k : LocalGL2 v) :
    gl2Entry v (g * k) 1 0 = gl2Entry v g 1 0 * gl2Entry v k 0 0 + gl2Entry v g 1 1 * gl2Entry v k 1 0 := by
  simp only [gl2Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem gl2Entry_mul_one_one (g k : LocalGL2 v) :
    gl2Entry v (g * k) 1 1 = gl2Entry v g 1 0 * gl2Entry v k 0 1 + gl2Entry v g 1 1 * gl2Entry v k 1 1 := by
  simp only [gl2Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem gl2Det_mul (g k : LocalGL2 v) : gl2Det v (g * k) = gl2Det v g * gl2Det v k := by
  simp only [gl2Det, Units.val_mul, Matrix.det_mul]

private theorem cornerEntry2_mul (g k : LocalGL2 v) :
    cornerEntry2 v (g * k) = cornerEntry2 v g * gl2Entry v k 0 0 + gl2Entry v g 1 1 * gl2Entry v k 1 0 :=
  gl2Entry_mul_one_zero v g k

private def IsNearOne (r : WithZero (Multiplicative ℤ)) (k : LocalGL2 v) : Prop :=
  Valued.v (gl2Entry v k 0 0 - 1) < r ∧ Valued.v (gl2Entry v k 1 1 - 1) < r ∧
    Valued.v (gl2Entry v k 0 1) < r ∧ Valued.v (gl2Entry v k 1 0) < r

private def IsSmallRadius (r : WithZero (Multiplicative ℤ)) : Prop :=
  ∀ b : v.adicCompletion ℚ, Valued.v b < r → Valued.v b < 1

variable {v}

private theorem valued_eq_one_of_sub_one_lt {r : WithZero (Multiplicative ℤ)} (hr : IsSmallRadius v r)
    {y : v.adicCompletion ℚ} (hy : Valued.v (y - 1) < r) : Valued.v y = 1 := by
  have h := Valuation.map_one_add_of_lt Valued.v (hr _ hy)
  rwa [add_sub_cancel] at h

private theorem ne_zero_of_sub_one_lt {r : WithZero (Multiplicative ℤ)} (hr : IsSmallRadius v r)
    {y : v.adicCompletion ℚ} (hy : Valued.v (y - 1) < r) : y ≠ 0 :=
  (Valuation.ne_zero_iff Valued.v).mp (by rw [valued_eq_one_of_sub_one_lt hr hy]; exact one_ne_zero)

private theorem norm_eq_one_of_sub_one_lt {r : WithZero (Multiplicative ℤ)} (hr : IsSmallRadius v r)
    {y : v.adicCompletion ℚ} (hy : Valued.v (y - 1) < r) : ‖y‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, valued_eq_one_of_sub_one_lt hr hy]
  simp

private theorem valued_mul_lt_of_le_one {r : WithZero (Multiplicative ℤ)} {a b : v.adicCompletion ℚ}
    (ha : Valued.v a ≤ 1) (hb : Valued.v b < r) : Valued.v (a * b) < r := by
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) hb

private theorem mul_sub_one_lt {r : WithZero (Multiplicative ℤ)} (hr : IsSmallRadius v r) {y z : v.adicCompletion ℚ}
    (hy : Valued.v (y - 1) < r) (hz : Valued.v (z - 1) < r) : Valued.v (y * z - 1) < r := by
  have h : y * z - 1 = (y - 1) * z + (z - 1) := by ring
  rw [h]
  refine Valuation.map_add_lt _ ?_ hz
  rw [map_mul, valued_eq_one_of_sub_one_lt hr hz, mul_one]
  exact hy

private theorem div_sub_one_lt {r : WithZero (Multiplicative ℤ)} (hr : IsSmallRadius v r) {y z : v.adicCompletion ℚ}
    (hy : Valued.v (y - 1) < r) (hz : Valued.v (z - 1) < r) : Valued.v (y / z - 1) < r := by
  have hz0 : z ≠ 0 := ne_zero_of_sub_one_lt hr hz
  have h : y / z - 1 = ((y - 1) - (z - 1)) / z := by
    field_simp
    ring
  rw [h, map_div₀, valued_eq_one_of_sub_one_lt hr hz, div_one]
  exact Valuation.map_sub_lt _ hy hz

private theorem add_sub_one_lt {r : WithZero (Multiplicative ℤ)} {y b : v.adicCompletion ℚ}
    (hy : Valued.v (y - 1) < r) (hb : Valued.v b < r) : Valued.v (y + b - 1) < r := by
  have h : y + b - 1 = (y - 1) + b := by ring
  rw [h]
  exact Valuation.map_add_lt _ hy hb

private theorem gl2Det_sub_one_lt {r : WithZero (Multiplicative ℤ)} (hr : IsSmallRadius v r) {k : LocalGL2 v}
    (hk : IsNearOne v r k) : Valued.v (gl2Det v k - 1) < r := by
  obtain ⟨h00, h11, h01, h10⟩ := hk
  have h : gl2Det v k - 1 = (gl2Entry v k 0 0 * gl2Entry v k 1 1 - 1) - gl2Entry v k 0 1 * gl2Entry v k 1 0 := by
    rw [gl2Det_eq]
    ring
  rw [h]
  exact Valuation.map_sub_lt _ (mul_sub_one_lt hr h00 h11)
    (valued_mul_lt_of_le_one (le_of_lt (hr _ h01)) h10)

private theorem charExt_mul_of_ne_zero (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0)
    (y : v.adicCompletion ℚ) : charExt χ (x * y) = charExt χ x * charExt χ y := by
  have h := charExt_units_mul (v := v) χ (Units.mk0 x hx) y
  rw [charExt_of_ne_zero χ hx]
  simpa only [Units.val_mk0] using h

private def IsLevelRadius (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (r : WithZero (Multiplicative ℤ)) :
    Prop :=
  {b : v.adicCompletion ℚ | Valued.v b < r} ∈ nhds (0 : v.adicCompletion ℚ) ∧ IsSmallRadius v r ∧
    ∀ i : Fin 2, ∀ y : v.adicCompletion ℚ, Valued.v (y - 1) < r → charExt (χ i) y = 1

private theorem cornerEntry2_mul_eq {r : WithZero (Multiplicative ℤ)} {k : LocalGL2 v} (hk : IsNearOne v r k)
    {g : LocalGL2 v} (hg : g ∈ cellCutoff2 v) :
    ∃ w : v.adicCompletion ℚ, Valued.v (w - 1) < r ∧ cornerEntry2 v (g * k) = cornerEntry2 v g * w := by
  obtain ⟨hc, hd⟩ := hg
  refine ⟨gl2Entry v k 0 0 + gl2Entry v g 1 1 / cornerEntry2 v g * gl2Entry v k 1 0, ?_, ?_⟩
  · exact add_sub_one_lt hk.1 (valued_mul_lt_of_le_one hd hk.2.2.2)
  · rw [cornerEntry2_mul]
    field_simp

private theorem mul_mem_cellCutoff2_of_mem {r : WithZero (Multiplicative ℤ)} (hr : IsSmallRadius v r) {k : LocalGL2 v}
    (hk : IsNearOne v r k) {g : LocalGL2 v} (hg : g ∈ cellCutoff2 v) : g * k ∈ cellCutoff2 v := by
  obtain ⟨w, hw, hcorner⟩ := cornerEntry2_mul_eq hk hg
  obtain ⟨hc, hd⟩ := hg
  have hw1 : Valued.v w = 1 := valued_eq_one_of_sub_one_lt hr hw
  have hw0 : w ≠ 0 := ne_zero_of_sub_one_lt hr hw
  refine ⟨by rw [hcorner]; exact mul_ne_zero hc hw0, ?_⟩
  have h : gl2Entry v (g * k) 1 1 / cornerEntry2 v (g * k)
      = (gl2Entry v k 0 1 + gl2Entry v g 1 1 / cornerEntry2 v g * gl2Entry v k 1 1) / w := by
    rw [hcorner, gl2Entry_mul_one_one, ← cornerEntry2]
    field_simp
  rw [h, map_div₀, hw1, div_one]
  refine Valuation.map_add_le _ (le_of_lt (hr _ hk.2.2.1)) ?_
  rw [map_mul, valued_eq_one_of_sub_one_lt hr hk.2.1, mul_one]
  exact hd

private theorem mul_notMem_cellCutoff2_of_notMem {r : WithZero (Multiplicative ℤ)} (hr : IsSmallRadius v r)
    {k : LocalGL2 v} (hk : IsNearOne v r k) {g : LocalGL2 v} (hg : g ∉ cellCutoff2 v) :
    g * k ∉ cellCutoff2 v := by
  intro hgk
  obtain ⟨hc', hd'⟩ := hgk
  apply hg
  have h00 : Valued.v (gl2Entry v k 0 0) = 1 := valued_eq_one_of_sub_one_lt hr hk.1
  have h11 : Valued.v (gl2Entry v k 1 1) = 1 := valued_eq_one_of_sub_one_lt hr hk.2.1
  have h01 : Valued.v (gl2Entry v k 0 1) < 1 := hr _ hk.2.2.1
  have h10 : Valued.v (gl2Entry v k 1 0) < 1 := hr _ hk.2.2.2

  by_cases hc : cornerEntry2 v g = 0
  ·

    exfalso
    have hd : gl2Entry v g 1 1 ≠ 0 := gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero v hc
    have hcorner : cornerEntry2 v (g * k) = gl2Entry v g 1 1 * gl2Entry v k 1 0 := by
      rw [cornerEntry2_mul, hc, zero_mul, zero_add]
    have hentry : gl2Entry v (g * k) 1 1 = gl2Entry v g 1 1 * gl2Entry v k 1 1 := by
      rw [gl2Entry_mul_one_one, ← cornerEntry2, hc, zero_mul, zero_add]
    have hk10 : gl2Entry v k 1 0 ≠ 0 := by
      intro h0
      exact hc' (by rw [hcorner, h0, mul_zero])
    have hlt : Valued.v (gl2Entry v (g * k) 1 1 / cornerEntry2 v (g * k)) > 1 := by
      rw [hentry, hcorner, map_div₀, map_mul, h11, mul_one, gt_iff_lt,
        one_lt_div₀ ((Valuation.pos_iff Valued.v).mpr (mul_ne_zero hd hk10)), map_mul]
      exact mul_lt_of_lt_one_right ((Valuation.pos_iff Valued.v).mpr hd) h10
    exact absurd hd' (not_le.mpr hlt)
  ·

    refine ⟨hc, ?_⟩
    by_contra hbig
    have hbig' : Valued.v (cornerEntry2 v g) < Valued.v (gl2Entry v g 1 1) := by
      rw [map_div₀] at hbig
      exact (one_lt_div₀ ((Valuation.pos_iff Valued.v).mpr hc)).mp (not_le.mp hbig)
    have hentry : Valued.v (gl2Entry v (g * k) 1 1) = Valued.v (gl2Entry v g 1 1) := by
      rw [gl2Entry_mul_one_one, ← cornerEntry2, Valuation.map_add_eq_of_lt_right, map_mul, h11, mul_one]
      rw [map_mul, map_mul, h11, mul_one]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (le_of_lt h01)) hbig'
    have hcorner : Valued.v (cornerEntry2 v (g * k)) < Valued.v (gl2Entry v g 1 1) := by
      rw [cornerEntry2_mul]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul, h00, mul_one]
        exact hbig'
      · rw [map_mul]
        exact mul_lt_of_lt_one_right (lt_of_le_of_lt _root_.zero_le hbig') h10
    have hlt : Valued.v (gl2Entry v (g * k) 1 1 / cornerEntry2 v (g * k)) > 1 := by
      rw [map_div₀, hentry, gt_iff_lt, one_lt_div₀ ((Valuation.pos_iff Valued.v).mpr hc')]
      exact hcorner
    exact absurd hd' (not_le.mpr hlt)

private theorem mul_mem_cellCutoff2_iff {r : WithZero (Multiplicative ℤ)} (hr : IsSmallRadius v r) {k : LocalGL2 v}
    (hk : IsNearOne v r k) (g : LocalGL2 v) : g * k ∈ cellCutoff2 v ↔ g ∈ cellCutoff2 v :=
  ⟨fun h => by_contra fun hg => mul_notMem_cellCutoff2_of_notMem hr hk hg h,
    fun hg => mul_mem_cellCutoff2_of_mem hr hk hg⟩

private theorem cellValue2_mul_of_mem {χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {r : WithZero (Multiplicative ℤ)} (hχ : IsLevelRadius χ r) {k : LocalGL2 v} (hk : IsNearOne v r k)
    {g : LocalGL2 v} (hg : g ∈ cellCutoff2 v) : cellValue2 v χ (g * k) = cellValue2 v χ g := by
  obtain ⟨-, hr, htriv⟩ := hχ
  obtain ⟨w, hw, hcorner⟩ := cornerEntry2_mul_eq hk hg
  have hc : cornerEntry2 v g ≠ 0 := hg.1
  have hw0 : w ≠ 0 := ne_zero_of_sub_one_lt hr hw
  have hdet : Valued.v (gl2Det v k - 1) < r := gl2Det_sub_one_lt hr hk
  have hq : Valued.v (gl2Det v k / w - 1) < r := div_sub_one_lt hr hdet hw
  have hratio0 : gl2Det v g / cornerEntry2 v g ≠ 0 := div_ne_zero (gl2Det_ne_zero v g) hc
  simp only [cellValue2, hcorner, gl2Det_mul, mul_div_mul_comm, charExt_mul_of_ne_zero (χ 0) hratio0,
    charExt_mul_of_ne_zero (χ 1) hc, htriv 0 _ hq, htriv 1 _ hw, norm_mul, norm_eq_one_of_sub_one_lt hr hw,
    norm_eq_one_of_sub_one_lt hr hq, mul_one]

private theorem cellSection2_mul {χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {r : WithZero (Multiplicative ℤ)}
    (hχ : IsLevelRadius χ r) {k : LocalGL2 v} (hk : IsNearOne v r k) (g : LocalGL2 v) :
    cellSection2 v χ (g * k) = cellSection2 v χ g := by
  by_cases hg : g ∈ cellCutoff2 v
  · rw [cellSection2, Set.indicator_of_mem ((mul_mem_cellCutoff2_iff hχ.2.1 hk g).mpr hg),
      Set.indicator_of_mem hg, cellValue2_mul_of_mem hχ hk hg]
  · rw [cellSection2, Set.indicator_of_notMem (fun h => hg ((mul_mem_cellCutoff2_iff hχ.2.1 hk g).mp h)),
      Set.indicator_of_notMem hg]

private theorem charExt_one (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) : charExt χ (1 : v.adicCompletion ℚ) = 1 := by
  rw [← Units.val_one, charExt_coe_units, map_one, Units.val_one]

private theorem eventually_valued_sub_one_lt_one :
    ∀ᶠ y : v.adicCompletion ℚ in nhds (1 : v.adicCompletion ℚ), Valued.v (y - 1) < 1 := by
  have h0 : {b : v.adicCompletion ℚ | (Valued.v : Valuation (v.adicCompletion ℚ)
      (WithZero (Multiplicative ℤ))).restrict b < (1 : Units _).1} ∈ nhds (0 : v.adicCompletion ℚ) :=
    Valued.mem_nhds_zero.mpr ⟨1, subset_rfl⟩
  have hcont : Continuous fun y : v.adicCompletion ℚ => y - 1 := continuous_id.sub continuous_const
  have h1 : (fun y : v.adicCompletion ℚ => y - 1) ⁻¹' {b : v.adicCompletion ℚ | (Valued.v : Valuation
      (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ))).restrict b < (1 : Units _).1} ∈
        nhds (1 : v.adicCompletion ℚ) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa only [sub_self] using h0)
  filter_upwards [h1] with y hy
  exact (Valuation.restrict_lt_one_iff _).mp hy

private theorem exists_isLevelRadius (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlc : ∀ i, IsLocallyConstant (χ i)) : ∃ r : WithZero (Multiplicative ℤ), IsLevelRadius χ r := by
  have h0 := eventually_charExt_eq (v := v) (χ 0) (hlc 0) (one_ne_zero : (1 : v.adicCompletion ℚ) ≠ 0)
  have h1 := eventually_charExt_eq (v := v) (χ 1) (hlc 1) (one_ne_zero : (1 : v.adicCompletion ℚ) ≠ 0)
  rw [charExt_one] at h0 h1
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ((h0.and h1).and (eventually_valued_sub_one_lt_one (v := v)))
  refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding γ.1, ?_, ?_, ?_⟩
  · refine Filter.mem_of_superset (Valued.mem_nhds_zero.mpr ⟨γ, subset_rfl⟩) fun b hb => ?_
    exact (Valuation.restrict_lt_iff_lt_embedding _).mp hb
  · intro b hb
    have hmem := hγ (show Valued.v.restrict ((1 + b) - 1) < γ.1 by
      rw [add_sub_cancel_left]
      exact (Valuation.restrict_lt_iff_lt_embedding _).mpr hb)
    simpa only [add_sub_cancel_left] using hmem.2
  · intro i y hy
    have hy' := hγ ((Valuation.restrict_lt_iff_lt_embedding _).mpr hy)
    fin_cases i
    · exact hy'.1.1
    · exact hy'.1.2

variable (v)

private def rightStabilizer (f : LocalGL2 v → ℂ) : Subgroup (LocalGL2 v) where
  carrier := {k | ∀ g, f (g * k) = f g}
  one_mem' := fun g => by rw [mul_one]
  mul_mem' := fun {a b} ha hb g => by rw [← mul_assoc, hb, ha]
  inv_mem' := fun {a} ha g => by
    have h := ha (g * a⁻¹)
    rw [inv_mul_cancel_right] at h
    exact h.symm

private theorem mem_rightStabilizer_iff {f : LocalGL2 v → ℂ} {k : LocalGL2 v} :
    k ∈ rightStabilizer v f ↔ ∀ g, f (g * k) = f g :=
  Iff.rfl

private theorem isNearOne_mem_nhds {r : WithZero (Multiplicative ℤ)}
    (hball : {b : v.adicCompletion ℚ | Valued.v b < r} ∈ nhds (0 : v.adicCompletion ℚ)) :
    {k : LocalGL2 v | IsNearOne v r k} ∈ nhds (1 : LocalGL2 v) := by
  have hentry : ∀ (i j : Fin 2) (c : v.adicCompletion ℚ), gl2Entry v (1 : LocalGL2 v) i j - c = 0 →
      {k : LocalGL2 v | Valued.v (gl2Entry v k i j - c) < r} ∈ nhds (1 : LocalGL2 v) := by
    intro i j c hc
    have hcont : Continuous fun k : LocalGL2 v => gl2Entry v k i j - c :=
      (continuous_gl2Entry v i j).sub continuous_const
    exact hcont.continuousAt.preimage_mem_nhds (by rw [hc]; exact hball)
  have h00 := hentry 0 0 1 (by simp [gl2Entry])
  have h11 := hentry 1 1 1 (by simp [gl2Entry])
  have h01 := hentry 0 1 0 (by simp [gl2Entry])
  have h10 := hentry 1 0 0 (by simp [gl2Entry])
  simp only [sub_zero] at h01 h10
  filter_upwards [h00, h11, h01, h10] with k hk00 hk11 hk01 hk10
  exact ⟨hk00, hk11, hk01, hk10⟩

private theorem exists_isOpen_forall_cellSection2_mul (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlc : ∀ i, IsLocallyConstant (χ i)) :
    ∃ K : Subgroup (LocalGL2 v), IsOpen (K : Set (LocalGL2 v)) ∧
      ∀ k ∈ K, ∀ g, cellSection2 v χ (g * k) = cellSection2 v χ g := by
  obtain ⟨r, hr⟩ := exists_isLevelRadius χ hlc
  refine ⟨rightStabilizer v (cellSection2 v χ), ?_, fun k hk => hk⟩
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (isNearOne_mem_nhds v hr.1) ?_)
  intro k hk g
  exact cellSection2_mul hr hk g

private theorem principalSeries2Rep_apply_eq {χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (u : ↥(principalSeries2 v χ)) {k : LocalGL2 v} (hk : ∀ g, (u : LocalGL2 v → ℂ) (g * k) = (u : LocalGL2 v → ℂ) g) :
    principalSeries2Rep (v := v) χ k u = u := by
  apply Subtype.ext
  funext g
  exact hk g

end Level
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

end LanglandsTunnell.CubicInduction.CellSectionLevel
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace CellSectionAdmissibility
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

p2m_open "IsDedekindDomain NumberField LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.CellSectionLevel P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.FixedVectorTransport"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_fixed_ne_zero_and_finiteDimensional_fixedVectors
    (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hlc : ∀ i, IsLocallyConstant (![θ, θ, θ'] i)) :
    ∃ (K₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) (u : ↥(principalSeries2 v ![θ, θ])),
      u ≠ 0 ∧ (∀ k ∈ K₁, (principalSeries2Rep (v := v) ![θ, θ]) k u = u) ∧
      FiniteDimensional ℂ
        ↥(FLT.SmoothAdmissibleSchurCommutant.fixedVectors (principalSeries2Rep (v := v) ![θ, θ]) K₁) := by
  have hlc₂ : ∀ i : Fin 2, IsLocallyConstant (![θ, θ] i) := fun i => by
    fin_cases i <;> exact hlc 0
  obtain ⟨K, hKopen, hKfix⟩ := exists_isOpen_forall_cellSection2_mul v ![θ, θ] hlc₂
  refine ⟨K, ⟨cellSection2 v ![θ, θ], cellSection2_mem_principalSeries2 v ![θ, θ] hlc₂⟩, ?_, ?_, ?_⟩
  · intro h
    exact cellSection2_antidiagonal2_ne_zero v ![θ, θ] (congrFun (congrArg Subtype.val h) (antidiagonal2 v))
  · intro k hk
    exact principalSeries2Rep_apply_eq v _ (hKfix k hk)
  · have hUopen : IsOpen ((K.map (glTransport v).toMonoidHom : Subgroup (GL (Fin 2) ℚ_[primeUnder v])) :
        Set (GL (Fin 2) ℚ_[primeUnder v])) :=
      isOpen_coe_map_of_isOpenMap (glTransport v) (isOpenMap_glTransport v) hKopen
    haveI : FiniteDimensional ℂ ↥(LocalNewvector.principalSeries (primeUnder v) (charTransport v (![θ, θ] 0))
        (charTransport v (![θ, θ] 1)) ⊓
          LocalNewvector.rightInvariantFunctions (primeUnder v) (K.map (glTransport v).toMonoidHom)) :=
      LocalNewvector.finiteDimensional_principalSeries_inf_rightInvariantFunctions (primeUnder v)
        (charTransport v (![θ, θ] 0)) (charTransport v (![θ, θ] 1)) (K.map (glTransport v).toMonoidHom) hUopen
    haveI : FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (K.map (glTransport v).toMonoidHom)
        (LocalNewvector.PSCarrier (primeUnder v) (charTransport v (![θ, θ] 0)) (charTransport v (![θ, θ] 1)))) :=
      (LocalNewvector.PSCarrier.fixedEquiv (primeUnder v) (charTransport v (![θ, θ] 0)) (charTransport v (![θ, θ] 1))
        (K.map (glTransport v).toMonoidHom)).symm.finiteDimensional
    exact finiteDimensional_fixedVectors_of_equiv (principalSeries2Rep (v := v) ![θ, θ]) (glTransport v)
      (carrierTransport v ![θ, θ]) (carrierTransport_principalSeries2Rep v ![θ, θ]) K

end LanglandsTunnell.CubicInduction.CellSectionAdmissibility
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction"

section

open Matrix Filter Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem continuous_diagonal3 : Continuous (diagonal3 v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_pi fun i : Fin 3 => Units.continuous_val.comp (continuous_apply i)).matrix_diagonal
  · exact (continuous_pi fun i : Fin 3 => Units.continuous_coe_inv.comp (continuous_apply i)).matrix_diagonal

private theorem halfModulus3_ne_zero (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : halfModulus3 v a ≠ 0 := by
  simp [halfModulus3, (a 0).ne_zero, (a 2).ne_zero]

private theorem isLocallyConstant_halfModulus3 : IsLocallyConstant (halfModulus3 v) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a

  have hc0 : Continuous fun b : Fin 3 → (v.adicCompletion ℚ)ˣ => (b 0 : v.adicCompletion ℚ) :=
    Units.continuous_val.comp (continuous_apply (0 : Fin 3))
  have hc2 : Continuous fun b : Fin 3 → (v.adicCompletion ℚ)ˣ => (b 2 : v.adicCompletion ℚ) :=
    Units.continuous_val.comp (continuous_apply (2 : Fin 3))
  have h0 : ∀ᶠ b : Fin 3 → (v.adicCompletion ℚ)ˣ in 𝓝 a,
      ‖(b 0 : v.adicCompletion ℚ)‖ = ‖(a 0 : v.adicCompletion ℚ)‖ :=
    (hc0.continuousAt (x := a)).eventually (eventually_norm_eq v (a 0).ne_zero)
  have h2 : ∀ᶠ b : Fin 3 → (v.adicCompletion ℚ)ˣ in 𝓝 a,
      ‖(b 2 : v.adicCompletion ℚ)‖ = ‖(a 2 : v.adicCompletion ℚ)‖ :=
    (hc2.continuousAt (x := a)).eventually (eventually_norm_eq v (a 2).ne_zero)
  filter_upwards [h0, h2] with b hb0 hb2
  simp only [halfModulus3, Function.comp_apply, hb0, hb2]

private theorem torusChar3_update_one (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (i : Fin 3)
    (u : (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ (Function.update (1 : Fin 3 → (v.adicCompletion ℚ)ˣ) i u) = ((χ i u : ℂˣ) : ℂ) := by
  unfold torusChar3
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Function.update_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem isLocallyConstant_of_mem_principalSeries3_of_ne_zero
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : LocalGL3 v → ℂ) (i : Fin 3) :
    f ∈ principalSeries3 v χ → f ≠ 0 → IsLocallyConstant (χ i) := by
  intro hf hne
  obtain ⟨g, hg⟩ := Function.ne_iff.1 hne
  have hg' : f g ≠ 0 := hg
  have hF : IsLocallyConstant fun a : Fin 3 → (v.adicCompletion ℚ)ˣ => f (diagonal3 v a * g) :=
    (isLocallyConstant_of_mem_principalSeries3 hf).comp_continuous
      ((continuous_diagonal3 v).mul continuous_const)
  simp_rw [apply_diagonal3_mul_of_mem_principalSeries3 hf] at hF
  have hTH : IsLocallyConstant fun a : Fin 3 → (v.adicCompletion ℚ)ˣ =>
      torusChar3 v χ a * halfModulus3 v a := by
    have h := hF.mul (IsLocallyConstant.const (f g)⁻¹)
    convert h using 1
    all_goals try rfl
    funext a
    simp only [Pi.mul_apply, Function.const_apply]
    field_simp
  have hT : IsLocallyConstant fun a : Fin 3 → (v.adicCompletion ℚ)ˣ => torusChar3 v χ a := by
    have h := hTH.mul ((isLocallyConstant_halfModulus3 v).comp fun z : ℂ => z⁻¹)
    convert h using 1
    all_goals try rfl
    funext a
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [mul_assoc, mul_inv_cancel₀ (halfModulus3_ne_zero v a), mul_one]
  have hc : IsLocallyConstant fun u : (v.adicCompletion ℚ)ˣ => ((χ i u : ℂˣ) : ℂ) := by
    have h := hT.comp_continuous
      (continuous_const.update i continuous_id :
        Continuous fun u : (v.adicCompletion ℚ)ˣ => Function.update (1 : Fin 3 → (v.adicCompletion ℚ)ˣ) i u)
    convert h using 1
    all_goals try rfl
    funext u
    exact (torusChar3_update_one v χ i u).symm
  rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
  intro u₀
  filter_upwards [hc u₀] with u hu
  exact Units.ext hu

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem principalSeries3_vanishOnParabolic_or_eq_of_isIrreducibleRep
    (v : HeightOneSpectrum (𝓞 ℚ))
    (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂]
    (π₂ : GL (Fin 2) (v.adicCompletion ℚ) →* Module.End ℂ V₂)
    (hI : FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep π₂)
    (hPσ : ∃ Ψ : ↥(principalSeries3 v ![θ, θ, θ']) →ₗ[ℂ] V₂, Function.Surjective Ψ ∧
        (∀ f : ↥(principalSeries3 v ![θ, θ, θ']), Ψ f = 0 ↔
          ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
            (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → (f : LocalGL3 v → ℂ) p = 0) ∧
        ∀ (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ)
          (f : ↥(principalSeries3 v ![θ, θ, θ'])),
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ) →
          (∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
            = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) →
          Ψ ⟨gl3AmbientRightTranslate (R := ℂ) p f, rightTranslate_mem_principalSeries3 f.2 p⟩
            = ((((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2)) /
              ‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) • (((θ' c : ℂˣ) : ℂ) • π₂ A (Ψ f))))
    :
    ∀ U : Submodule ℂ (LocalGL3 v → ℂ), U ≤ principalSeries3 v ![θ, θ, θ'] →
        (∀ f ∈ principalSeries3 v ![θ, θ, θ'],
          (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
            (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) → f ∈ U) →
        (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 →
          U ≤ U.comap (gl3AmbientRightTranslate (R := ℂ) p)) →
        (∀ f ∈ U, ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) ∨
          U = principalSeries3 v ![θ, θ, θ'] := by
  obtain ⟨Ψ, -, hker, hlaw⟩ := hPσ
  intro U hU hVP hstab

  set W : Submodule ℂ V₂ := (U.comap (principalSeries3 v ![θ, θ, θ']).subtype).map Ψ
  have hmemW : ∀ x : ↥(principalSeries3 v ![θ, θ, θ']), (x : LocalGL3 v → ℂ) ∈ U → Ψ x ∈ W := fun x hx =>
    Submodule.mem_map_of_mem (Submodule.mem_comap.mpr hx)

  have hA20 : ∀ A : GL (Fin 2) (v.adicCompletion ℚ),
      ((iotaGL A : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 := by
    intro A; simp [embedMat2]
  have hA21 : ∀ A : GL (Fin 2) (v.adicCompletion ℚ),
      ((iotaGL A : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 := by
    intro A; simp [embedMat2]
  have hA22 : ∀ A : GL (Fin 2) (v.adicCompletion ℚ),
      ((iotaGL A : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2
        = ((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by
    intro A; simp [embedMat2]
  have hAblk : ∀ A : GL (Fin 2) (v.adicCompletion ℚ), ∀ i j : Fin 2,
      ((iotaGL A : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
        = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j := by
    intro A i j; fin_cases i <;> fin_cases j <;> simp [embedMat2]

  have hWstable : ∀ (A : GL (Fin 2) (v.adicCompletion ℚ)), ∀ w ∈ W, π₂ A w ∈ W := by
    intro A w hw
    obtain ⟨x, hxU', rfl⟩ := Submodule.mem_map.mp hw
    have hxU : (x : LocalGL3 v → ℂ) ∈ U := Submodule.mem_comap.mp hxU'
    have hyU : gl3AmbientRightTranslate (R := ℂ) (iotaGL A : LocalGL3 v) x ∈ U :=
      Submodule.mem_comap.mp (hstab (iotaGL A) (hA20 A) (hA21 A) hxU)
    have hyW := hmemW ⟨gl3AmbientRightTranslate (R := ℂ) (iotaGL A : LocalGL3 v) x,
      rightTranslate_mem_principalSeries3 x.2 (iotaGL A)⟩ hyU
    rw [hlaw (iotaGL A) A 1 x (hA20 A) (hA21 A) (hA22 A) (hAblk A)] at hyW
    simp only [map_one, Units.val_one, one_smul, norm_one, div_one] at hyW
    have hdet : (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit A)).ne_zero
    have hs : ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr hdet) _).ne'
    have hinv := W.smul_mem
      ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ)⁻¹ hyW
    rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at hinv
  rcases hI.2 W hWstable with hbot | htop
  ·
    left
    intro f hf p hp20 hp21
    have hfW := hmemW ⟨f, hU hf⟩ hf
    rw [hbot, Submodule.mem_bot] at hfW
    exact (hker ⟨f, hU hf⟩).mp hfW p hp20 hp21
  ·
    right
    refine le_antisymm hU ?_
    intro g hg
    have hgW : Ψ ⟨g, hg⟩ ∈ W := by rw [htop]; exact Submodule.mem_top
    obtain ⟨x, hxU', hx⟩ := Submodule.mem_map.mp hgW
    have hxU : (x : LocalGL3 v → ℂ) ∈ U := Submodule.mem_comap.mp hxU'
    have hdiff : Ψ ((⟨g, hg⟩ : ↥(principalSeries3 v ![θ, θ, θ'])) - x) = 0 := by
      rw [map_sub, hx, sub_self]
    have hvan := (hker _).mp hdiff
    have hdU : g - (x : LocalGL3 v → ℂ) ∈ U :=
      hVP _ ((principalSeries3 v ![θ, θ, θ']).sub_mem hg x.2) (fun p hp20 hp21 => hvan p hp20 hp21)
    have hsum := U.add_mem hdU hxU
    rwa [sub_add_cancel] at hsum

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace LevelLattice
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

section Transversal

variable {G : Type*} [AddCommGroup G]

private theorem exists_finset_transversal (A' A : AddSubgroup G) [Finite (A ⧸ A'.addSubgroupOf A)] :
    ∃ T : Finset G, (∀ p ∈ T, p ∈ A) ∧ (∀ a ∈ A, ∃ p ∈ T, a - p ∈ A') ∧
      (∀ p ∈ T, ∀ p' ∈ T, p - p' ∈ A' → p = p') ∧ T.card = Nat.card (A ⧸ A'.addSubgroupOf A) := by
  classical
  haveI : Fintype (A ⧸ A'.addSubgroupOf A) := Fintype.ofFinite _
  let rep : A ⧸ A'.addSubgroupOf A → G := fun q => ((Quotient.out q : A) : G)
  have hrep : Function.Injective rep := fun q q' h => Quotient.out_injective (Subtype.ext h)
  refine ⟨Finset.univ.image rep, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    exact (Quotient.out q).2
  · intro a ha
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul (s := A'.addSubgroupOf A) (⟨a, ha⟩ : A)
    refine ⟨rep (QuotientAddGroup.mk ⟨a, ha⟩), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have hcoe : rep (QuotientAddGroup.mk ⟨a, ha⟩) = a + ((h : A) : G) := by
      show ((Quotient.out (QuotientAddGroup.mk (⟨a, ha⟩ : A)) : A) : G) = a + ((h : A) : G)
      rw [hh]
      rfl
    rw [hcoe, sub_add_cancel_left]
    exact A'.neg_mem (AddSubgroup.mem_addSubgroupOf.mp h.2)
  · intro p hp p' hp' hpp'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hp'
    congr 1
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq]
    refine AddSubgroup.mem_addSubgroupOf.mpr ?_
    have : -(rep q) + rep q' ∈ A' := by
      rw [neg_add_eq_sub, ← neg_sub]
      exact A'.neg_mem hpp'
    exact this
  · rw [Finset.card_image_of_injective _ hrep, Finset.card_univ, Nat.card_eq_fintype_card]

end Transversal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

section Indicator

variable {G : Type*} [AddCommGroup G]

open Classical in

private noncomputable def cosetPairIndicator (A : AddSubgroup G) (p q : G) : G → G → ℂ :=
  fun x y => if x - p ∈ A ∧ y - q ∈ A then 1 else 0

private theorem cosetPairIndicator_of_mem {A : AddSubgroup G} {p q x y : G} (hx : x - p ∈ A) (hy : y - q ∈ A) :
    cosetPairIndicator A p q x y = 1 := by
  unfold cosetPairIndicator
  exact if_pos ⟨hx, hy⟩

private theorem cosetPairIndicator_of_not {A : AddSubgroup G} {p q x y : G} (h : ¬(x - p ∈ A ∧ y - q ∈ A)) :
    cosetPairIndicator A p q x y = 0 := by
  unfold cosetPairIndicator
  exact if_neg h

private theorem cosetPairIndicator_add (A : AddSubgroup G) (p q d₁ d₂ x y : G) :
    cosetPairIndicator A p q (x + d₁) (y + d₂) = cosetPairIndicator A (p - d₁) (q - d₂) x y := by
  unfold cosetPairIndicator
  rw [show x + d₁ - p = x - (p - d₁) by abel, show y + d₂ - q = y - (q - d₂) by abel]

private theorem eq_sum_cosetPairIndicator (A' A : AddSubgroup G) (T : Finset G)
    (hT : ∀ a ∈ A, ∃ p ∈ T, a - p ∈ A') (hT' : ∀ p ∈ T, ∀ p' ∈ T, p - p' ∈ A' → p = p')
    (φ : G → G → ℂ) (hinv : ∀ x y d₁ d₂ : G, d₁ ∈ A' → d₂ ∈ A' → φ (x + d₁) (y + d₂) = φ x y)
    (hsupp : ∀ x y : G, φ x y ≠ 0 → x ∈ A ∧ y ∈ A) :
    φ = fun x y => ∑ p ∈ T, ∑ q ∈ T, φ p q * cosetPairIndicator A' p q x y := by
  funext x y
  by_cases h : ∃ p ∈ T, ∃ q ∈ T, x - p ∈ A' ∧ y - q ∈ A'
  · obtain ⟨p, hp, q, hq, hxp, hyq⟩ := h
    have hφ : φ x y = φ p q := by
      have e := hinv p q (x - p) (y - q) hxp hyq
      rw [show p + (x - p) = x by abel, show q + (y - q) = y by abel] at e
      exact e
    rw [hφ, Finset.sum_eq_single p, Finset.sum_eq_single q]
    · rw [cosetPairIndicator_of_mem hxp hyq, mul_one]
    · intro q' hq' hne
      rw [cosetPairIndicator_of_not, mul_zero]
      rintro ⟨-, hyq'⟩
      exact hne (hT' q' hq' q hq (by rw [show q' - q = (y - q) - (y - q') by abel]; exact A'.sub_mem hyq hyq'))
    · intro hq'
      exact (hq' hq).elim
    · intro p' hp' hne
      refine Finset.sum_eq_zero fun q' _ => ?_
      rw [cosetPairIndicator_of_not, mul_zero]
      rintro ⟨hxp', -⟩
      exact hne (hT' p' hp' p hp (by rw [show p' - p = (x - p) - (x - p') by abel]; exact A'.sub_mem hxp hxp'))
    · intro hp'
      exact (hp' hp).elim
  · have hzero : ∀ p ∈ T, ∀ q ∈ T, cosetPairIndicator A' p q x y = 0 :=
      fun p hp q hq => cosetPairIndicator_of_not fun hh => h ⟨p, hp, q, hq, hh⟩
    have hφ : φ x y = 0 := by
      by_contra hne
      obtain ⟨hxA, hyA⟩ := hsupp x y hne
      obtain ⟨p, hp, hxp⟩ := hT x hxA
      obtain ⟨q, hq, hyq⟩ := hT y hyA
      exact h ⟨p, hp, q, hq, hxp, hyq⟩
    rw [hφ]
    symm
    exact Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => by rw [hzero p hp q hq, mul_zero]

open Classical in

private noncomputable def cosetIndicator (A : AddSubgroup G) (p : G) : G → ℂ :=
  fun x => if x - p ∈ A then 1 else 0

private theorem cosetIndicator_of_mem {A : AddSubgroup G} {p x : G} (hx : x - p ∈ A) : cosetIndicator A p x = 1 := by
  unfold cosetIndicator
  exact if_pos hx

private theorem cosetIndicator_of_not {A : AddSubgroup G} {p x : G} (h : x - p ∉ A) : cosetIndicator A p x = 0 := by
  unfold cosetIndicator
  exact if_neg h

private theorem cosetIndicator_add (A : AddSubgroup G) (p d x : G) :
    cosetIndicator A p (x + d) = cosetIndicator A (p - d) x := by
  unfold cosetIndicator
  rw [show x + d - p = x - (p - d) by abel]

private theorem eq_sum_cosetIndicator (A' A : AddSubgroup G) (T : Finset G)
    (hT : ∀ a ∈ A, ∃ p ∈ T, a - p ∈ A') (hT' : ∀ p ∈ T, ∀ p' ∈ T, p - p' ∈ A' → p = p')
    (φ : G → ℂ) (hinv : ∀ x d : G, d ∈ A' → φ (x + d) = φ x) (hsupp : ∀ x : G, φ x ≠ 0 → x ∈ A) :
    φ = fun x => ∑ p ∈ T, φ p * cosetIndicator A' p x := by
  funext x
  by_cases h : ∃ p ∈ T, x - p ∈ A'
  · obtain ⟨p, hp, hxp⟩ := h
    have hφ : φ x = φ p := by
      have e := hinv p (x - p) hxp
      rw [show p + (x - p) = x by abel] at e
      exact e
    rw [hφ, Finset.sum_eq_single p]
    · rw [cosetIndicator_of_mem hxp, mul_one]
    · intro p' hp' hne
      rw [cosetIndicator_of_not, mul_zero]
      intro hxp'
      exact hne (hT' p' hp' p hp (by rw [show p' - p = (x - p) - (x - p') by abel]; exact A'.sub_mem hxp hxp'))
    · intro hp'
      exact (hp' hp).elim
  · have hzero : ∀ p ∈ T, cosetIndicator A' p x = 0 := fun p hp => cosetIndicator_of_not fun hh => h ⟨p, hp, hh⟩
    have hφ : φ x = 0 := by
      by_contra hne
      obtain ⟨p, hp, hxp⟩ := hT x (hsupp x hne)
      exact h ⟨p, hp, hxp⟩
    rw [hφ]
    symm
    exact Finset.sum_eq_zero fun p hp => by rw [hzero p hp, mul_zero]

end Indicator
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

section Dilation

variable {F : Type*} [Field F]

private noncomputable def _root_.LanglandsTunnell.CubicInduction.LevelLattice.dilate (c : F) (A : AddSubgroup F) : AddSubgroup F :=
  A.comap (AddMonoidHom.mulLeft c)

p2m_export "LanglandsTunnell.CubicInduction.LevelLattice" "dilate"
private theorem mem_dilate {c : F} {A : AddSubgroup F} {x : F} : x ∈ dilate c A ↔ c * x ∈ A :=
  Iff.rfl

private theorem cosetPairIndicator_mul (A : AddSubgroup F) (c : F) (hc : c ≠ 0) (hle : A ≤ dilate c A)
    (T : Finset F) (hTsub : ∀ r ∈ T, r ∈ dilate c A) (hT : ∀ a ∈ dilate c A, ∃ r ∈ T, a - r ∈ A)
    (hT' : ∀ r ∈ T, ∀ r' ∈ T, r - r' ∈ A → r = r') (p q : F) :
    (fun x y => cosetPairIndicator A p q (c * x) (c * y)) =
      fun x y => ∑ r ∈ T, ∑ s ∈ T, cosetPairIndicator A (c⁻¹ * p + r) (c⁻¹ * q + s) x y := by

  set ψ : F → F → ℂ := fun x y => cosetPairIndicator A p q (c * (x + c⁻¹ * p)) (c * (y + c⁻¹ * q)) with hψ
  have hkey : ∀ x y : F, c * (x + c⁻¹ * p) - p = c * x ∧ c * (y + c⁻¹ * q) - q = c * y := fun x y => by
    refine ⟨?_, ?_⟩ <;> rw [mul_add, mul_inv_cancel_left₀ hc, add_sub_cancel_right]
  have hψ1 : ∀ x y : F, c * x ∈ A → c * y ∈ A → ψ x y = 1 := fun x y hx hy => by
    rw [hψ]
    exact cosetPairIndicator_of_mem (by rwa [(hkey x y).1]) (by rwa [(hkey x y).2])
  have hψ0 : ∀ x y : F, ¬(c * x ∈ A ∧ c * y ∈ A) → ψ x y = 0 := fun x y h => by
    rw [hψ]
    exact cosetPairIndicator_of_not (by rwa [(hkey x y).1, (hkey x y).2])
  have hinv : ∀ x y d₁ d₂ : F, d₁ ∈ A → d₂ ∈ A → ψ (x + d₁) (y + d₂) = ψ x y := by
    intro x y d₁ d₂ h₁ h₂
    have h₁' : c * d₁ ∈ A := hle h₁
    have h₂' : c * d₂ ∈ A := hle h₂
    by_cases hxy : c * x ∈ A ∧ c * y ∈ A
    · rw [hψ1 x y hxy.1 hxy.2, hψ1 (x + d₁) (y + d₂) (by rw [mul_add]; exact A.add_mem hxy.1 h₁')
        (by rw [mul_add]; exact A.add_mem hxy.2 h₂')]
    · rw [hψ0 x y hxy, hψ0 (x + d₁) (y + d₂) ?_]
      rintro ⟨hx, hy⟩
      rw [mul_add] at hx hy
      exact hxy ⟨by simpa using A.sub_mem hx h₁', by simpa using A.sub_mem hy h₂'⟩
  have hsupp : ∀ x y : F, ψ x y ≠ 0 → x ∈ dilate c A ∧ y ∈ dilate c A := by
    intro x y hne
    by_contra hh
    exact hne (hψ0 x y fun hxy => hh ⟨mem_dilate.mpr hxy.1, mem_dilate.mpr hxy.2⟩)
  have hexp := eq_sum_cosetPairIndicator A (dilate c A) T hT hT' ψ hinv hsupp
  have hone : ∀ r ∈ T, ∀ s ∈ T, ψ r s = 1 := fun r hr s hs =>
    hψ1 r s (mem_dilate.mp (hTsub r hr)) (mem_dilate.mp (hTsub s hs))
  funext x y
  show cosetPairIndicator A p q (c * x) (c * y) =
    ∑ r ∈ T, ∑ s ∈ T, cosetPairIndicator A (c⁻¹ * p + r) (c⁻¹ * q + s) x y
  have hshift : cosetPairIndicator A p q (c * x) (c * y) = ψ (x - c⁻¹ * p) (y - c⁻¹ * q) := by
    simp only [hψ, sub_add_cancel]
  have hx := congrFun (congrFun hexp (x - c⁻¹ * p)) (y - c⁻¹ * q)
  beta_reduce at hx
  rw [hshift, hx]
  refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun s hs => ?_
  rw [hone r hr s hs, one_mul, sub_eq_add_neg, sub_eq_add_neg, cosetPairIndicator_add,
    show r - -(c⁻¹ * p) = c⁻¹ * p + r by abel, show s - -(c⁻¹ * q) = c⁻¹ * q + s by abel]

private theorem cosetIndicator_mul (A : AddSubgroup F) (c : F) (hc : c ≠ 0) (hle : A ≤ dilate c A)
    (T : Finset F) (hTsub : ∀ r ∈ T, r ∈ dilate c A) (hT : ∀ a ∈ dilate c A, ∃ r ∈ T, a - r ∈ A)
    (hT' : ∀ r ∈ T, ∀ r' ∈ T, r - r' ∈ A → r = r') (p : F) :
    (fun x => cosetIndicator A p (c * x)) = fun x => ∑ r ∈ T, cosetIndicator A (c⁻¹ * p + r) x := by
  set ψ : F → ℂ := fun x => cosetIndicator A p (c * (x + c⁻¹ * p)) with hψ
  have hkey : ∀ x : F, c * (x + c⁻¹ * p) - p = c * x := fun x => by
    rw [mul_add, mul_inv_cancel_left₀ hc, add_sub_cancel_right]
  have hψ1 : ∀ x : F, c * x ∈ A → ψ x = 1 := fun x hx => by
    rw [hψ]
    exact cosetIndicator_of_mem (by rwa [hkey x])
  have hψ0 : ∀ x : F, c * x ∉ A → ψ x = 0 := fun x h => by
    rw [hψ]
    exact cosetIndicator_of_not (by rwa [hkey x])
  have hinv : ∀ x d : F, d ∈ A → ψ (x + d) = ψ x := by
    intro x d h₁
    have h₁' : c * d ∈ A := hle h₁
    by_cases hx : c * x ∈ A
    · rw [hψ1 x hx, hψ1 (x + d) (by rw [mul_add]; exact A.add_mem hx h₁')]
    · rw [hψ0 x hx, hψ0 (x + d) ?_]
      intro hxd
      rw [mul_add] at hxd
      exact hx (by simpa using A.sub_mem hxd h₁')
  have hsupp : ∀ x : F, ψ x ≠ 0 → x ∈ dilate c A := by
    intro x hne
    by_contra hh
    exact hne (hψ0 x fun hx => hh (mem_dilate.mpr hx))
  have hexp := eq_sum_cosetIndicator A (dilate c A) T hT hT' ψ hinv hsupp
  have hone : ∀ r ∈ T, ψ r = 1 := fun r hr => hψ1 r (mem_dilate.mp (hTsub r hr))
  funext x
  show cosetIndicator A p (c * x) = ∑ r ∈ T, cosetIndicator A (c⁻¹ * p + r) x
  have hshift : cosetIndicator A p (c * x) = ψ (x - c⁻¹ * p) := by
    simp only [hψ, sub_add_cancel]
  have hx := congrFun hexp (x - c⁻¹ * p)
  beta_reduce at hx
  rw [hshift, hx]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [hone r hr, one_mul, sub_eq_add_neg, cosetIndicator_add, show r - -(c⁻¹ * p) = c⁻¹ * p + r by abel]

end Dilation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

section LevelBall

variable {F : Type*} [Field F] [Valued F (WithZero (Multiplicative ℤ))]

private noncomputable def levelBall (m : ℤ) : AddSubgroup F where
  carrier := {x | Valued.v x ≤ WithZero.exp m}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => (Valued.v.map_add a b).trans (max_le ha hb)
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq, Valuation.map_neg] at ha ⊢
    exact ha

private theorem mem_levelBall {m : ℤ} {x : F} : x ∈ levelBall (F := F) m ↔ Valued.v x ≤ WithZero.exp m :=
  Iff.rfl

private theorem levelBall_mono {m m' : ℤ} (h : m ≤ m') : levelBall (F := F) m ≤ levelBall m' :=
  fun _ hx => le_trans hx (WithZero.exp_le_exp.mpr h)

private theorem levelBall_le_dilate {m : ℤ} {c : F} (hc : Valued.v c ≤ 1) :
    levelBall (F := F) m ≤ dilate c (levelBall m) := by
  intro x hx
  rw [mem_dilate, mem_levelBall, Valuation.map_mul]
  exact le_trans (mul_le_of_le_one_left' hc) hx

private theorem mem_dilate_levelBall_iff {m n : ℤ} {c : F} (hc : Valued.v c = WithZero.exp n) (x : F) :
    x ∈ dilate c (levelBall (F := F) m) ↔ x ∈ levelBall (F := F) (m - n) := by
  have hc0 : c ≠ 0 := fun h => by
    rw [h, Valuation.map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  rw [mem_dilate, mem_levelBall, mem_levelBall]
  constructor
  · intro h
    rw [show x = c⁻¹ * (c * x) by rw [inv_mul_cancel_left₀ hc0], Valuation.map_mul, map_inv₀, hc,
      ← WithZero.exp_neg, show m - n = -n + m by abel, WithZero.exp_add]
    exact mul_le_mul_right h _
  · intro h
    rw [Valuation.map_mul, hc, show m = n + (m - n) by abel, WithZero.exp_add]
    exact mul_le_mul_right h _

private theorem dilate_levelBall_eq {m n : ℤ} {c : F} (hc : Valued.v c = WithZero.exp n) :
    dilate c (levelBall (F := F) m) = levelBall (m - n) :=
  AddSubgroup.ext (mem_dilate_levelBall_iff hc)

end LevelBall
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

end LanglandsTunnell.CubicInduction.LevelLattice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem toAdd_unzero_exp_int (n : ℤ) (h : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero h) = n :=
  rfl

private theorem norm_uniformizerUnit_eq_inv_absNorm (v : HeightOneSpectrum (𝓞 ℚ)) :
    ‖(NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ)‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, NumberField.AdelicLevel.valued_uniformizerUnit,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, toAdd_unzero_exp_int]
  simp

private theorem uniformizerUnit_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 ℚ)) :
    (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, NumberField.AdelicLevel.valued_uniformizerUnit,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  norm_num

private noncomputable def integralUniformizer (v : HeightOneSpectrum (𝓞 ℚ)) : ↥(v.adicCompletionIntegers ℚ) :=
  ⟨NumberField.AdelicLevel.uniformizerUnit ℚ v, uniformizerUnit_mem_adicCompletionIntegers v⟩

private theorem coe_integralUniformizer (v : HeightOneSpectrum (𝓞 ℚ)) :
    (integralUniformizer v : v.adicCompletion ℚ) =
      (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ) :=
  rfl

private theorem maximalIdeal_eq_span_integralUniformizer (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers ℚ) = Ideal.span {integralUniformizer v} := by
  have hϖ : (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ) ≠ 0 := Units.ne_zero _
  apply le_antisymm
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact Ideal.zero_mem _
    rw [NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one] at hx
    have hxK : (x : v.adicCompletion ℚ) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hvx : Valued.v (x : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hxK

    have hle : Valued.v (x : v.adicCompletion ℚ) ≤ WithZero.exp (-1 : ℤ) := by
      rw [← WithZero.exp_log hvx] at hx ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
      rw [WithZero.exp_le_exp]
      omega
    have hy : (x : v.adicCompletion ℚ) / (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ) ∈
        v.adicCompletionIntegers ℚ := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, NumberField.AdelicLevel.valued_uniformizerUnit]
      rw [← WithZero.exp_log hvx] at hle ⊢
      rw [WithZero.exp_le_exp] at hle
      rw [← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    refine Ideal.mem_span_singleton'.mpr ⟨⟨_, hy⟩, ?_⟩
    exact Subtype.ext (div_mul_cancel₀ _ hϖ)
  · rw [Ideal.span_singleton_le_iff_mem, NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one,
      coe_integralUniformizer, NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zero,
      WithZero.exp_lt_exp]
    norm_num

private theorem irreducible_integralUniformizer (v : HeightOneSpectrum (𝓞 ℚ)) : Irreducible (integralUniformizer v) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr (maximalIdeal_eq_span_integralUniformizer v)

private theorem natCard_quot_maximalIdeal (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (↥(v.adicCompletionIntegers ℚ) ⧸ IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers ℚ)) =
      Ideal.absNorm v.asIdeal := by
  let f : 𝓞 ℚ ⧸ v.asIdeal →+* IsLocalRing.ResidueField ↥(v.adicCompletionIntegers ℚ) :=
    Ideal.Quotient.lift v.asIdeal
      ((IsLocalRing.residue ↥(v.adicCompletionIntegers ℚ)).comp (algebraMap (𝓞 ℚ) ↥(v.adicCompletionIntegers ℚ)))
      (fun a ha => NumberField.AdelicHaar.residue_algebraMap_eq_zero_of_mem (𝓞 ℚ) ℚ v ha)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨a, ha⟩ := NumberField.AdelicHaar.residue_algebraMap_surjective (𝓞 ℚ) ℚ v z
    exact ⟨Ideal.Quotient.mk _ a, ha⟩
  have hker : RingHom.ker ((IsLocalRing.residue ↥(v.adicCompletionIntegers ℚ)).comp
      (algebraMap (𝓞 ℚ) ↥(v.adicCompletionIntegers ℚ))) ≤ v.asIdeal := by
    intro a ha
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
      NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one] at ha
    simp only [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply] at ha
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap] at ha
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v a).mp ha
  have hinj : Function.Injective f := RingHom.lift_injective_of_ker_le_ideal v.asIdeal _ hker
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (RingEquiv.ofBijective f hbij).toEquiv).symm

private theorem valued_coe_unit_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) (u : (↥(v.adicCompletionIntegers ℚ))ˣ) :
    Valued.v ((u : ↥(v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ) = 1 := by
  have h1 : Valued.v ((u : ↥(v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ) ≤ 1 :=
    (u : ↥(v.adicCompletionIntegers ℚ)).2
  have h2 : Valued.v (((u⁻¹ : (↥(v.adicCompletionIntegers ℚ))ˣ) : ↥(v.adicCompletionIntegers ℚ)) :
      v.adicCompletion ℚ) ≤ 1 :=
    ((u⁻¹ : (↥(v.adicCompletionIntegers ℚ))ˣ) : ↥(v.adicCompletionIntegers ℚ)).2
  have hmul : Valued.v ((u : ↥(v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ) *
      Valued.v (((u⁻¹ : (↥(v.adicCompletionIntegers ℚ))ˣ) : ↥(v.adicCompletionIntegers ℚ)) :
        v.adicCompletion ℚ) = 1 := by
    rw [← map_mul, show ((u : ↥(v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ) *
        (((u⁻¹ : (↥(v.adicCompletionIntegers ℚ))ˣ) : ↥(v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ) =
        (((u : ↥(v.adicCompletionIntegers ℚ)) * ((u⁻¹ : (↥(v.adicCompletionIntegers ℚ))ˣ) :
          ↥(v.adicCompletionIntegers ℚ)) : ↥(v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ) from rfl,
      Units.mul_inv]
    simp
  exact le_antisymm h1 (hmul ▸ mul_le_of_le_one_right' h2)

private theorem norm_coe_unit_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) (u : (↥(v.adicCompletionIntegers ℚ))ˣ) :
    ‖((u : ↥(v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ)‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, valued_coe_unit_eq_one, map_one, NNReal.coe_one]

set_option synthInstance.maxHeartbeats 1600000 in

private theorem natCard_quot_span_singleton_eq_inv_norm (v : HeightOneSpectrum (𝓞 ℚ))
    (a : ↥(v.adicCompletionIntegers ℚ)) (ha : a ≠ 0) :
    ((Nat.card (↥(v.adicCompletionIntegers ℚ) ⧸ Ideal.span {a}) : ℕ) : ℝ) = ‖(a : v.adicCompletion ℚ)‖⁻¹ := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha (irreducible_integralUniformizer v)
  have hspan : Ideal.span {(u : ↥(v.adicCompletionIntegers ℚ)) * integralUniformizer v ^ n} =
      IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers ℚ) ^ n := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      maximalIdeal_eq_span_integralUniformizer]
  rw [hspan, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field _),
    Submodule.cardQuot_apply, natCard_quot_maximalIdeal]
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_integralUniformizer]
  rw [norm_mul, norm_pow, norm_coe_unit_eq_one, norm_uniformizerUnit_eq_inv_absNorm, one_mul, inv_pow, inv_inv]
  exact Nat.cast_pow _ _

end LanglandsTunnell.CubicInduction
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace LevelLattice
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem mem_span_singleton_iff_valued_le (v : HeightOneSpectrum (𝓞 ℚ))
    (c : ↥(v.adicCompletionIntegers ℚ)) (hc : c ≠ 0) (y : ↥(v.adicCompletionIntegers ℚ)) :
    y ∈ Ideal.span {c} ↔ Valued.v (y : v.adicCompletion ℚ) ≤ Valued.v (c : v.adicCompletion ℚ) := by
  have hcK : (c : v.adicCompletion ℚ) ≠ 0 := fun h => hc (Subtype.ext h)
  constructor
  · intro hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [Subring.coe_mul, map_mul]
    exact mul_le_of_le_one_left' z.2
  · intro hy
    have hz : (y : v.adicCompletion ℚ) / (c : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
      exact div_le_one_of_le₀ hy (zero_le')
    refine Ideal.mem_span_singleton'.mpr ⟨⟨_, hz⟩, ?_⟩
    exact Subtype.ext (div_mul_cancel₀ _ hcK)

private theorem valued_mul_le_exp_iff (v : HeightOneSpectrum (𝓞 ℚ)) {π : v.adicCompletion ℚ} {k : ℤ}
    (hπ : Valued.v π = WithZero.exp k) (x : v.adicCompletion ℚ) (l : ℤ) :
    Valued.v (π * x) ≤ WithZero.exp l ↔ Valued.v x ≤ WithZero.exp (l - k) := by
  rw [map_mul, hπ]
  by_cases hx : Valued.v x = 0
  · simp [hx]
  rw [← WithZero.exp_log hx, ← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
  omega

set_option synthInstance.maxHeartbeats 1600000 in

private theorem finite_and_natCard_dilate_levelBall (v : HeightOneSpectrum (𝓞 ℚ)) (m n : ℤ) (hn : n ≤ 0)
    (c : v.adicCompletion ℚ) (hc : Valued.v c = WithZero.exp n) :
    Finite (↥(dilate c (levelBall (F := v.adicCompletion ℚ) m)) ⧸
        (levelBall m).addSubgroupOf (dilate c (levelBall m))) ∧
      ((Nat.card (↥(dilate c (levelBall (F := v.adicCompletion ℚ) m)) ⧸
        (levelBall m).addSubgroupOf (dilate c (levelBall m))) : ℕ) : ℝ) = ‖c‖⁻¹ := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact WithZero.exp_ne_zero hc.symm
  have hcO : c ∈ v.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hc, ← WithZero.exp_zero, WithZero.exp_le_exp]; exact hn
  set a : ↥(v.adicCompletionIntegers ℚ) := ⟨c, hcO⟩ with ha_def
  have ha : a ≠ 0 := fun h => hc0 (congrArg Subtype.val h)

  set π : v.adicCompletion ℚ :=
    (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ) ^ (m - n) with hπ_def
  have hπ : Valued.v π = WithZero.exp (n - m) := by
    rw [hπ_def, map_zpow₀, NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zsmul, smul_eq_mul]
    congr 1; ring
  have hπ0 : π ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
  have hbig : ∀ x : v.adicCompletion ℚ,
      x ∈ dilate c (levelBall (F := v.adicCompletion ℚ) m) ↔ Valued.v (π * x) ≤ 1 := by
    intro x
    rw [mem_dilate_levelBall_iff hc, mem_levelBall, ← WithZero.exp_zero, valued_mul_le_exp_iff v hπ]
    constructor <;> intro h <;> convert h using 2 <;> ring
  have hsmall : ∀ x : v.adicCompletion ℚ,
      x ∈ levelBall (F := v.adicCompletion ℚ) m ↔ Valued.v (π * x) ≤ Valued.v (a : v.adicCompletion ℚ) := by
    intro x
    rw [mem_levelBall, ha_def, hc, valued_mul_le_exp_iff v hπ]
    constructor <;> intro h <;> convert h using 2 <;> ring
  have hmem : ∀ x : ↥(dilate c (levelBall (F := v.adicCompletion ℚ) m)),
      π * (x : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ :=
    fun x => (hbig x).mp x.2
  let φ : ↥(dilate c (levelBall (F := v.adicCompletion ℚ) m)) →+ (↥(v.adicCompletionIntegers ℚ) ⧸ Ideal.span {a}) :=
    AddMonoidHom.mk' (fun x => Ideal.Quotient.mk _ ⟨π * x, hmem x⟩) (by
      intro x y
      beta_reduce
      rw [← map_add]
      congr 1
      exact Subtype.ext (by simp [mul_add]))
  have hφ : ∀ x, φ x = Ideal.Quotient.mk _ ⟨π * x, hmem x⟩ := fun _ => rfl
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hx : π⁻¹ * (y : v.adicCompletion ℚ) ∈ dilate c (levelBall (F := v.adicCompletion ℚ) m) := by
      rw [hbig, mul_inv_cancel_left₀ hπ0]
      exact y.2
    refine ⟨⟨_, hx⟩, ?_⟩
    rw [hφ]
    congr 1
    apply Subtype.ext
    simp [mul_inv_cancel_left₀ hπ0]
  have hker : φ.ker = (levelBall m).addSubgroupOf (dilate c (levelBall (F := v.adicCompletion ℚ) m)) := by
    ext x
    rw [AddMonoidHom.mem_ker, hφ, Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton_iff_valued_le v a ha,
      AddSubgroup.mem_addSubgroupOf, hsmall]
  let e : (↥(dilate c (levelBall (F := v.adicCompletion ℚ) m)) ⧸
        (levelBall m).addSubgroupOf (dilate c (levelBall m))) ≃+ (↥(v.adicCompletionIntegers ℚ) ⧸ Ideal.span {a}) :=
    (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj)
  have hcard : ((Nat.card (↥(dilate c (levelBall (F := v.adicCompletion ℚ) m)) ⧸
        (levelBall m).addSubgroupOf (dilate c (levelBall m))) : ℕ) : ℝ) = ‖c‖⁻¹ := by
    rw [Nat.card_congr e.toEquiv, natCard_quot_span_singleton_eq_inv_norm v a ha]
  refine ⟨?_, hcard⟩
  apply Nat.finite_of_card_ne_zero
  intro h0
  rw [h0, Nat.cast_zero] at hcard
  exact inv_ne_zero (norm_ne_zero_iff.mpr hc0) hcard.symm

end LanglandsTunnell.CubicInduction.LevelLattice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem radical_mul (v : HeightOneSpectrum (𝓞 ℚ)) (x y x' y' : v.adicCompletion ℚ) :
    (upperUnipotent3 0 y x : LocalGL3 v) * upperUnipotent3 0 y' x' = upperUnipotent3 0 (y + y') (x + x') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

private theorem radical_mul_center (v : HeightOneSpectrum (𝓞 ℚ)) (x y : v.adicCompletion ℚ)
    (c : (v.adicCompletion ℚ)ˣ) :
    (upperUnipotent3 0 y x : LocalGL3 v) * diagonal3 v ![1, 1, c] =
      diagonal3 v ![1, 1, c] * upperUnipotent3 0 ((c : v.adicCompletion ℚ) * y) ((c : v.adicCompletion ℚ) * x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm]

private theorem antidiagonal3_mul_center (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ) :
    antidiagonal3 v * diagonal3 v ![1, 1, c] = diagonal3 v ![c, 1, 1] * antidiagonal3 v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, antidiagonal3_coe]

private theorem rightTranslate_radical_apply (v : HeightOneSpectrum (𝓞 ℚ)) (f : LocalGL3 v → ℂ) (q : LocalGL3 v)
    (x y x' y' : v.adicCompletion ℚ) :
    gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 0 y' x') f (q * upperUnipotent3 0 y x) =
      f (q * upperUnipotent3 0 (y + y') (x + x')) := by
  rw [gl3AmbientRightTranslate_apply, mul_assoc, radical_mul]

private theorem rightTranslate_center_apply (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (q : LocalGL3 v) (c : (v.adicCompletion ℚ)ˣ) (d : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (hq : q * diagonal3 v ![1, 1, c] = diagonal3 v d * q) (x y : v.adicCompletion ℚ) :
    gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) f (q * upperUnipotent3 0 y x) =
      torusChar3 v χ d * halfModulus3 v d *
        f (q * upperUnipotent3 0 ((c : v.adicCompletion ℚ) * y) ((c : v.adicCompletion ℚ) * x)) := by
  rw [gl3AmbientRightTranslate_apply, mul_assoc, radical_mul_center, ← mul_assoc, hq, mul_assoc,
    apply_diagonal3_mul_of_mem_principalSeries3 hf]

private theorem law_factor_open (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (c : (v.adicCompletion ℚ)ˣ) :
    torusChar3 v ![θ, θ, θ'] ![c, 1, 1] * halfModulus3 v ![c, 1, 1] =
      ((θ c : ℂˣ) : ℂ) * ((‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
  simp [torusChar3, halfModulus3, Fin.prod_univ_three]

private theorem law_factor_middle (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (c : (v.adicCompletion ℚ)ˣ) :
    torusChar3 v ![θ, θ, θ'] ![1, c, 1] * halfModulus3 v ![1, c, 1] = ((θ c : ℂˣ) : ℂ) := by
  simp [torusChar3, halfModulus3, Fin.prod_univ_three]

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private noncomputable def radicalX (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) : v.adicCompletion ℚ :=
  (gl3Entry v g 1 2 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 2) / lowerMinor v g

private noncomputable def radicalY (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) : v.adicCompletion ℚ :=
  outerMinor v g / lowerMinor v g

private noncomputable def leviOfFirst (v : HeightOneSpectrum (𝓞 ℚ)) (t : v.adicCompletion ℚ) : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![t, 1, 0; 1, 0, 0; 0, 0, (1 : v.adicCompletion ℚ)] (by
    simp [Matrix.det_fin_three])

private theorem leviOfFirst_coe (v : HeightOneSpectrum (𝓞 ℚ)) (t : v.adicCompletion ℚ) :
    (leviOfFirst v t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = !![t, 1, 0; 1, 0, 0; 0, 0, 1] :=
  rfl

private noncomputable def baseOfFirst (v : HeightOneSpectrum (𝓞 ℚ)) (t : v.adicCompletion ℚ) : LocalGL3 v :=
  antidiagonal3 v * leviOfFirst v t

private noncomputable def baseOfZeroth (v : HeightOneSpectrum (𝓞 ℚ)) (s : v.adicCompletion ℚ) : LocalGL3 v :=
  antidiagonal3 v * upperUnipotent3 s 0 0

private theorem baseOfFirst_coe (v : HeightOneSpectrum (𝓞 ℚ)) (t : v.adicCompletion ℚ) :
    (baseOfFirst v t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = !![0, 0, 1; 1, 0, 0; t, 1, 0] := by
  rw [baseOfFirst, Units.val_mul, antidiagonal3_coe, leviOfFirst_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem baseOfZeroth_coe (v : HeightOneSpectrum (𝓞 ℚ)) (s : v.adicCompletion ℚ) :
    (baseOfZeroth v s : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = !![0, 0, 1; 0, 1, 0; 1, s, 0] := by
  rw [baseOfZeroth, Units.val_mul, antidiagonal3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem baseOfFirst_mul_center (v : HeightOneSpectrum (𝓞 ℚ)) (t : v.adicCompletion ℚ)
    (c : (v.adicCompletion ℚ)ˣ) :
    baseOfFirst v t * diagonal3 v ![1, 1, c] = diagonal3 v ![c, 1, 1] * baseOfFirst v t := by
  ext i j
  rw [Units.val_mul, Units.val_mul, baseOfFirst_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

private theorem baseOfZeroth_mul_center (v : HeightOneSpectrum (𝓞 ℚ)) (s : v.adicCompletion ℚ)
    (c : (v.adicCompletion ℚ)ˣ) :
    baseOfZeroth v s * diagonal3 v ![1, 1, c] = diagonal3 v ![c, 1, 1] * baseOfZeroth v s := by
  ext i j
  rw [Units.val_mul, Units.val_mul, baseOfZeroth_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

private theorem law_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (d : Fin 3 → (v.adicCompletion ℚ)ˣ) : torusChar3 v χ d * halfModulus3 v d ≠ 0 := by
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero _) ?_
  rw [halfModulus3]
  exact_mod_cast (div_pos (norm_pos_iff.mpr (d 0).ne_zero) (norm_pos_iff.mpr (d 2).ne_zero)).ne'

private theorem eq_mul_baseOfFirst (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (hL : lowerMinor v g ≠ 0)
    (h21 : gl3Entry v g 2 1 ≠ 0) :
    ∃ (a b e : v.adicCompletion ℚ) (d : Fin 3 → (v.adicCompletion ℚ)ˣ),
      g = upperUnipotent3 a b e * (diagonal3 v d *
        (baseOfFirst v (gl3Entry v g 2 0 / gl3Entry v g 2 1) * upperUnipotent3 0 (radicalY v g) (radicalX v g))) := by
  have hdet : gl3Det v g ≠ 0 := gl3Det_ne_zero v g
  refine ⟨(gl3Entry v g 0 0 * gl3Entry v g 2 1 - gl3Entry v g 0 1 * gl3Entry v g 2 0) / lowerMinor v g,
    gl3Entry v g 1 1 / gl3Entry v g 2 1, gl3Entry v g 0 1 / gl3Entry v g 2 1,
    ![Units.mk0 _ (div_ne_zero hdet hL), Units.mk0 _ (div_ne_zero hL h21), Units.mk0 _ h21], ?_⟩
  have h21' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 ≠ 0 := h21
  ext i j
  simp only [Units.val_mul, diagonal3_coe, upperUnipotent3_coe, baseOfFirst_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal, radicalX, radicalY, outerMinor, gl3Det, gl3Entry,
      Matrix.det_fin_three] <;>
    (try field_simp) <;> (try simp only [lowerMinor, gl3Entry]) <;> ring1

private theorem eq_mul_baseOfZeroth (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (hL : lowerMinor v g ≠ 0)
    (h20 : gl3Entry v g 2 0 ≠ 0) :
    ∃ (a b e : v.adicCompletion ℚ) (d : Fin 3 → (v.adicCompletion ℚ)ˣ),
      g = upperUnipotent3 a b e * (diagonal3 v d *
        (baseOfZeroth v (gl3Entry v g 2 1 / gl3Entry v g 2 0) * upperUnipotent3 0 (radicalY v g) (radicalX v g))) := by
  have hdet : gl3Det v g ≠ 0 := gl3Det_ne_zero v g
  have hL' : -lowerMinor v g / gl3Entry v g 2 0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hL) h20
  refine ⟨-(gl3Entry v g 0 1 * gl3Entry v g 2 0 - gl3Entry v g 0 0 * gl3Entry v g 2 1) / lowerMinor v g,
    gl3Entry v g 1 0 / gl3Entry v g 2 0, gl3Entry v g 0 0 / gl3Entry v g 2 0,
    ![Units.mk0 _ (div_ne_zero hdet hL), Units.mk0 _ hL', Units.mk0 _ h20], ?_⟩
  have h20' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 ≠ 0 := h20
  ext i j
  simp only [Units.val_mul, diagonal3_coe, upperUnipotent3_coe, baseOfZeroth_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal, radicalX, radicalY, outerMinor, gl3Det, gl3Entry,
      Matrix.det_fin_three] <;>
    (try field_simp) <;> (try simp only [lowerMinor, gl3Entry]) <;> ring1

private theorem apply_eq_of_first (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (g : LocalGL3 v) (hL : lowerMinor v g ≠ 0)
    (h21 : gl3Entry v g 2 1 ≠ 0) :
    ∃ d : Fin 3 → (v.adicCompletion ℚ)ˣ, f g = torusChar3 v χ d * halfModulus3 v d *
      f (baseOfFirst v (gl3Entry v g 2 0 / gl3Entry v g 2 1) * upperUnipotent3 0 (radicalY v g) (radicalX v g)) := by
  obtain ⟨a, b, e, d, hg⟩ := eq_mul_baseOfFirst v g hL h21
  refine ⟨d, ?_⟩
  conv_lhs => rw [hg]
  rw [apply_upperUnipotent3_mul_of_mem_principalSeries3 hf, apply_diagonal3_mul_of_mem_principalSeries3 hf]

private theorem apply_eq_of_zeroth (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (g : LocalGL3 v) (hL : lowerMinor v g ≠ 0)
    (h20 : gl3Entry v g 2 0 ≠ 0) :
    ∃ d : Fin 3 → (v.adicCompletion ℚ)ˣ, f g = torusChar3 v χ d * halfModulus3 v d *
      f (baseOfZeroth v (gl3Entry v g 2 1 / gl3Entry v g 2 0) * upperUnipotent3 0 (radicalY v g) (radicalX v g)) := by
  obtain ⟨a, b, e, d, hg⟩ := eq_mul_baseOfZeroth v g hL h20
  refine ⟨d, ?_⟩
  conv_lhs => rw [hg]
  rw [apply_upperUnipotent3_mul_of_mem_principalSeries3 hf, apply_diagonal3_mul_of_mem_principalSeries3 hf]

private theorem entry_ne_zero_of_lowerMinor_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (hL : lowerMinor v g ≠ 0) : gl3Entry v g 2 0 ≠ 0 ∨ gl3Entry v g 2 1 ≠ 0 := by
  by_contra h
  push Not at h
  apply hL
  rw [lowerMinor, h.1, h.2]
  ring

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private noncomputable def midBaseOfZeroth (v : HeightOneSpectrum (𝓞 ℚ)) (s : v.adicCompletion ℚ) : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1, 0; 0, 0, 1; (1 : v.adicCompletion ℚ), s, 0] (by
    simp [Matrix.det_fin_three])

private theorem midBaseOfZeroth_coe (v : HeightOneSpectrum (𝓞 ℚ)) (s : v.adicCompletion ℚ) :
    (midBaseOfZeroth v s : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![0, 1, 0; 0, 0, 1; (1 : v.adicCompletion ℚ), s, 0] :=
  rfl

private noncomputable def midBaseOfFirst (v : HeightOneSpectrum (𝓞 ℚ)) (t : v.adicCompletion ℚ) : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : v.adicCompletion ℚ), 0, 0; 0, 0, 1; t, 1, 0] (by
    simp [Matrix.det_fin_three])

private theorem midBaseOfFirst_coe (v : HeightOneSpectrum (𝓞 ℚ)) (t : v.adicCompletion ℚ) :
    (midBaseOfFirst v t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(1 : v.adicCompletion ℚ), 0, 0; 0, 0, 1; t, 1, 0] :=
  rfl

private theorem midBaseOfZeroth_mul_center (v : HeightOneSpectrum (𝓞 ℚ)) (s : v.adicCompletion ℚ)
    (c : (v.adicCompletion ℚ)ˣ) :
    midBaseOfZeroth v s * diagonal3 v ![1, 1, c] = diagonal3 v ![1, c, 1] * midBaseOfZeroth v s := by
  ext i j
  rw [Units.val_mul, Units.val_mul, midBaseOfZeroth_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

private theorem midBaseOfFirst_mul_center (v : HeightOneSpectrum (𝓞 ℚ)) (t : v.adicCompletion ℚ)
    (c : (v.adicCompletion ℚ)ˣ) :
    midBaseOfFirst v t * diagonal3 v ![1, 1, c] = diagonal3 v ![1, c, 1] * midBaseOfFirst v t := by
  ext i j
  rw [Units.val_mul, Units.val_mul, midBaseOfFirst_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

private theorem midBaseOfZeroth_mul_radical (v : HeightOneSpectrum (𝓞 ℚ)) (s x y : v.adicCompletion ℚ) :
    midBaseOfZeroth v s * upperUnipotent3 0 y x =
      upperUnipotent3 y 0 0 * (midBaseOfZeroth v s * upperUnipotent3 0 0 (x + s * y)) := by
  ext i j
  simp only [Units.val_mul, midBaseOfZeroth_coe, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem midBaseOfFirst_mul_radical (v : HeightOneSpectrum (𝓞 ℚ)) (t x y : v.adicCompletion ℚ) :
    midBaseOfFirst v t * upperUnipotent3 0 y x =
      upperUnipotent3 x 0 0 * (midBaseOfFirst v t * upperUnipotent3 0 (x * t + y) 0) := by
  ext i j
  simp only [Units.val_mul, midBaseOfFirst_coe, upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring1

private theorem apply_midBaseOfZeroth_mul_radical (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (s x y : v.adicCompletion ℚ) :
    f (midBaseOfZeroth v s * upperUnipotent3 0 y x) = f (midBaseOfZeroth v s * upperUnipotent3 0 0 (x + s * y)) := by
  rw [midBaseOfZeroth_mul_radical, apply_upperUnipotent3_mul_of_mem_principalSeries3 hf]

private theorem apply_midBaseOfFirst_mul_radical (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (t x y : v.adicCompletion ℚ) :
    f (midBaseOfFirst v t * upperUnipotent3 0 y x) = f (midBaseOfFirst v t * upperUnipotent3 0 (x * t + y) 0) := by
  rw [midBaseOfFirst_mul_radical, apply_upperUnipotent3_mul_of_mem_principalSeries3 hf]

private theorem entry_mul_gl3Det (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) :
    gl3Entry v g 2 1 * gl3Det v g =
      (gl3Entry v g 0 0 * gl3Entry v g 2 1 - gl3Entry v g 0 1 * gl3Entry v g 2 0) *
          (gl3Entry v g 1 1 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 1)
        + (gl3Entry v g 0 2 * gl3Entry v g 2 1 - gl3Entry v g 0 1 * gl3Entry v g 2 2) * lowerMinor v g := by
  simp only [gl3Det, gl3Entry, lowerMinor, Matrix.det_fin_three]
  ring

private theorem cofactor_ne_zero_of_lowerMinor_eq_zero (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (hL : lowerMinor v g = 0) (h21 : gl3Entry v g 2 1 ≠ 0) :
    gl3Entry v g 1 1 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 1 ≠ 0 := by
  intro hM
  apply gl3Det_ne_zero v g
  have h := entry_mul_gl3Det v g
  rw [hM, hL, mul_zero, mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left h21

private theorem eq_mul_midBaseOfZeroth (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (hL : lowerMinor v g = 0)
    (h20 : gl3Entry v g 2 0 ≠ 0) :
    ∃ (a b e : v.adicCompletion ℚ) (d : Fin 3 → (v.adicCompletion ℚ)ˣ),
      g = upperUnipotent3 a b e * (diagonal3 v d * (midBaseOfZeroth v (gl3Entry v g 2 1 / gl3Entry v g 2 0) *
        upperUnipotent3 0 0 (gl3Entry v g 2 2 / gl3Entry v g 2 0))) := by
  have hdet : gl3Det v g ≠ 0 := gl3Det_ne_zero v g
  have hO : outerMinor v g ≠ 0 := outerMinor_ne_zero_of_lowerMinor_eq_zero v h20 hL
  have h11 : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 =
      (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 /
        (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 := by
    have h20' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 ≠ 0 := h20
    simp only [lowerMinor, gl3Entry] at hL
    field_simp
    linear_combination -hL
  refine ⟨(gl3Entry v g 0 0 * gl3Entry v g 2 2 - gl3Entry v g 0 2 * gl3Entry v g 2 0) / outerMinor v g,
    gl3Entry v g 1 0 / gl3Entry v g 2 0, gl3Entry v g 0 0 / gl3Entry v g 2 0,
    ![Units.mk0 _ (neg_ne_zero.mpr (div_ne_zero hdet hO)), Units.mk0 _ (neg_ne_zero.mpr (div_ne_zero hO h20)),
      Units.mk0 _ h20], ?_⟩
  have h20' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 ≠ 0 := h20
  ext i j
  simp only [Units.val_mul, diagonal3_coe, upperUnipotent3_coe, midBaseOfZeroth_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal, gl3Det, gl3Entry, Matrix.det_fin_three, h11] <;>
    (try field_simp) <;> (try simp only [outerMinor, gl3Entry]) <;> ring1

private theorem eq_mul_midBaseOfFirst (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (hL : lowerMinor v g = 0)
    (h21 : gl3Entry v g 2 1 ≠ 0) :
    ∃ (a b e : v.adicCompletion ℚ) (d : Fin 3 → (v.adicCompletion ℚ)ˣ),
      g = upperUnipotent3 a b e * (diagonal3 v d * (midBaseOfFirst v (gl3Entry v g 2 0 / gl3Entry v g 2 1) *
        upperUnipotent3 0 (gl3Entry v g 2 2 / gl3Entry v g 2 1) 0)) := by
  have hdet : gl3Det v g ≠ 0 := gl3Det_ne_zero v g
  have hM := cofactor_ne_zero_of_lowerMinor_eq_zero v g hL h21
  have h10 : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 =
      (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 /
        (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 := by
    have h21' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 ≠ 0 := h21
    simp only [lowerMinor, gl3Entry] at hL
    field_simp
    linear_combination hL
  generalize hMdef : gl3Entry v g 1 1 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 1 = M at hM
  refine ⟨(gl3Entry v g 0 1 * gl3Entry v g 2 2 - gl3Entry v g 0 2 * gl3Entry v g 2 1) / M,
    gl3Entry v g 1 1 / gl3Entry v g 2 1, gl3Entry v g 0 1 / gl3Entry v g 2 1,
    ![Units.mk0 _ (div_ne_zero hdet hM), Units.mk0 _ (neg_ne_zero.mpr (div_ne_zero hM h21)), Units.mk0 _ h21], ?_⟩
  have h21' : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 ≠ 0 := h21
  ext i j
  simp only [Units.val_mul, diagonal3_coe, upperUnipotent3_coe, midBaseOfFirst_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal, gl3Det, gl3Entry, Matrix.det_fin_three, h10] <;>
    (try field_simp) <;> (subst hMdef; try simp only [gl3Entry]) <;> ring1

private theorem apply_eq_of_mid_zeroth (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (g : LocalGL3 v) (hL : lowerMinor v g = 0)
    (h20 : gl3Entry v g 2 0 ≠ 0) :
    ∃ d : Fin 3 → (v.adicCompletion ℚ)ˣ, f g = torusChar3 v χ d * halfModulus3 v d *
      f (midBaseOfZeroth v (gl3Entry v g 2 1 / gl3Entry v g 2 0) *
        upperUnipotent3 0 0 (gl3Entry v g 2 2 / gl3Entry v g 2 0)) := by
  obtain ⟨a, b, e, d, hg⟩ := eq_mul_midBaseOfZeroth v g hL h20
  refine ⟨d, ?_⟩
  conv_lhs => rw [hg]
  rw [apply_upperUnipotent3_mul_of_mem_principalSeries3 hf, apply_diagonal3_mul_of_mem_principalSeries3 hf]

private theorem apply_eq_of_mid_first (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (g : LocalGL3 v) (hL : lowerMinor v g = 0)
    (h21 : gl3Entry v g 2 1 ≠ 0) :
    ∃ d : Fin 3 → (v.adicCompletion ℚ)ˣ, f g = torusChar3 v χ d * halfModulus3 v d *
      f (midBaseOfFirst v (gl3Entry v g 2 0 / gl3Entry v g 2 1) *
        upperUnipotent3 0 (gl3Entry v g 2 2 / gl3Entry v g 2 1) 0) := by
  obtain ⟨a, b, e, d, hg⟩ := eq_mul_midBaseOfFirst v g hL h21
  refine ⟨d, ?_⟩
  conv_lhs => rw [hg]
  rw [apply_upperUnipotent3_mul_of_mem_principalSeries3 hf, apply_diagonal3_mul_of_mem_principalSeries3 hf]

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem radicalX_upperUnipotent3_mul (v : HeightOneSpectrum (𝓞 ℚ)) (a b e : v.adicCompletion ℚ)
    (g : LocalGL3 v) : radicalX v (upperUnipotent3 a b e * g) = radicalX v g := by
  simp only [radicalX, lowerMinor_upperUnipotent3_mul, gl3Entry_upperUnipotent3_mul_one,
    gl3Entry_upperUnipotent3_mul_two]
  congr 1
  ring1

private theorem radicalY_upperUnipotent3_mul (v : HeightOneSpectrum (𝓞 ℚ)) (a b e : v.adicCompletion ℚ)
    (g : LocalGL3 v) : radicalY v (upperUnipotent3 a b e * g) = radicalY v g := by
  simp only [radicalY, lowerMinor_upperUnipotent3_mul, outerMinor_upperUnipotent3_mul]

private theorem radicalX_diagonal3_mul (v : HeightOneSpectrum (𝓞 ℚ)) (d : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) : radicalX v (diagonal3 v d * g) = radicalX v g := by
  have h : ((d 1 : v.adicCompletion ℚ) * d 2) ≠ 0 := mul_ne_zero (d 1).ne_zero (d 2).ne_zero
  simp only [radicalX, lowerMinor_diagonal3_mul, gl3Entry_diagonal3_mul]
  rw [show (d 1 : v.adicCompletion ℚ) * gl3Entry v g 1 2 * ((d 2 : v.adicCompletion ℚ) * gl3Entry v g 2 1)
        - (d 1 : v.adicCompletion ℚ) * gl3Entry v g 1 1 * ((d 2 : v.adicCompletion ℚ) * gl3Entry v g 2 2)
      = ((d 1 : v.adicCompletion ℚ) * d 2) *
          (gl3Entry v g 1 2 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 2)
      by ring, mul_div_mul_left _ _ h]

private theorem radicalY_diagonal3_mul (v : HeightOneSpectrum (𝓞 ℚ)) (d : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) : radicalY v (diagonal3 v d * g) = radicalY v g := by
  have h : ((d 1 : v.adicCompletion ℚ) * d 2) ≠ 0 := mul_ne_zero (d 1).ne_zero (d 2).ne_zero
  simp only [radicalY, lowerMinor_diagonal3_mul, outerMinor_diagonal3_mul, mul_div_mul_left _ _ h]

private theorem section_baseOfFirst (v : HeightOneSpectrum (𝓞 ℚ)) (t x y : v.adicCompletion ℚ) :
    gl3Entry v (baseOfFirst v t * upperUnipotent3 0 y x) 2 0 = t ∧
      gl3Entry v (baseOfFirst v t * upperUnipotent3 0 y x) 2 1 = 1 ∧
      lowerMinor v (baseOfFirst v t * upperUnipotent3 0 y x) = 1 ∧
      radicalX v (baseOfFirst v t * upperUnipotent3 0 y x) = x ∧
      radicalY v (baseOfFirst v t * upperUnipotent3 0 y x) = y := by
  simp only [radicalX, radicalY, lowerMinor, outerMinor, gl3Entry, Units.val_mul, baseOfFirst_coe, upperUnipotent3_coe]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring1

private theorem section_baseOfZeroth (v : HeightOneSpectrum (𝓞 ℚ)) (s x y : v.adicCompletion ℚ) :
    gl3Entry v (baseOfZeroth v s * upperUnipotent3 0 y x) 2 0 = 1 ∧
      gl3Entry v (baseOfZeroth v s * upperUnipotent3 0 y x) 2 1 = s ∧
      lowerMinor v (baseOfZeroth v s * upperUnipotent3 0 y x) = -1 ∧
      radicalX v (baseOfZeroth v s * upperUnipotent3 0 y x) = x ∧
      radicalY v (baseOfZeroth v s * upperUnipotent3 0 y x) = y := by
  simp only [radicalX, radicalY, lowerMinor, outerMinor, gl3Entry, Units.val_mul, baseOfZeroth_coe,
    upperUnipotent3_coe]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring1

private theorem section_midBaseOfZeroth (v : HeightOneSpectrum (𝓞 ℚ)) (s r : v.adicCompletion ℚ) :
    lowerMinor v (midBaseOfZeroth v s * upperUnipotent3 0 0 r) = 0 ∧
      gl3Entry v (midBaseOfZeroth v s * upperUnipotent3 0 0 r) 2 0 = 1 ∧
      gl3Entry v (midBaseOfZeroth v s * upperUnipotent3 0 0 r) 2 1 = s ∧
      gl3Entry v (midBaseOfZeroth v s * upperUnipotent3 0 0 r) 2 2 = r := by
  simp only [lowerMinor, gl3Entry, Units.val_mul, midBaseOfZeroth_coe, upperUnipotent3_coe]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem section_midBaseOfFirst (v : HeightOneSpectrum (𝓞 ℚ)) (t r : v.adicCompletion ℚ) :
    lowerMinor v (midBaseOfFirst v t * upperUnipotent3 0 r 0) = 0 ∧
      gl3Entry v (midBaseOfFirst v t * upperUnipotent3 0 r 0) 2 0 = t ∧
      gl3Entry v (midBaseOfFirst v t * upperUnipotent3 0 r 0) 2 1 = 1 ∧
      gl3Entry v (midBaseOfFirst v t * upperUnipotent3 0 r 0) 2 2 = r := by
  simp only [lowerMinor, gl3Entry, Units.val_mul, midBaseOfFirst_coe, upperUnipotent3_coe]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private noncomputable def oppositeRadical (v : HeightOneSpectrum (𝓞 ℚ)) (a b : v.adicCompletion ℚ) : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : v.adicCompletion ℚ), 0, 0; 0, 1, 0; a, b, 1] (by
    simp [Matrix.det_fin_three])

private theorem oppositeRadical_coe (v : HeightOneSpectrum (𝓞 ℚ)) (a b : v.adicCompletion ℚ) :
    (oppositeRadical v a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(1 : v.adicCompletion ℚ), 0, 0; 0, 1, 0; a, b, 1] :=
  rfl

private theorem gl3Entry_oppositeRadical (v : HeightOneSpectrum (𝓞 ℚ)) (a b : v.adicCompletion ℚ) :
    gl3Entry v (oppositeRadical v a b) 2 0 = a ∧ gl3Entry v (oppositeRadical v a b) 2 1 = b ∧
      (∀ i, gl3Entry v (oppositeRadical v a b) i i = 1) ∧
      gl3Entry v (oppositeRadical v a b) 0 1 = 0 ∧ gl3Entry v (oppositeRadical v a b) 0 2 = 0 ∧
      gl3Entry v (oppositeRadical v a b) 1 0 = 0 ∧ gl3Entry v (oppositeRadical v a b) 1 2 = 0 := by
  refine ⟨rfl, rfl, fun i => ?_, rfl, rfl, rfl, rfl⟩
  fin_cases i <;> rfl

private theorem gl3Entry_mul_oppositeRadical (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (a b : v.adicCompletion ℚ) :
    gl3Entry v (g * oppositeRadical v a b) 2 0 = gl3Entry v g 2 0 + a * gl3Entry v g 2 2 ∧
      gl3Entry v (g * oppositeRadical v a b) 2 1 = gl3Entry v g 2 1 + b * gl3Entry v g 2 2 ∧
      gl3Entry v (g * oppositeRadical v a b) 2 2 = gl3Entry v g 2 2 := by
  simp only [gl3Entry, Units.val_mul, oppositeRadical_coe]
  refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring1

private theorem lowerMinor_mul_oppositeRadical (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (a b : v.adicCompletion ℚ) :
    lowerMinor v (g * oppositeRadical v a b) =
      lowerMinor v g + a * (gl3Entry v g 1 2 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 2)
        + b * outerMinor v g := by
  simp only [lowerMinor, outerMinor, gl3Entry, Units.val_mul, oppositeRadical_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring1

private theorem lowerMinor_mul_oppositeRadical_of_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (hL : lowerMinor v g ≠ 0) (a b : v.adicCompletion ℚ) :
    lowerMinor v (g * oppositeRadical v a b) = lowerMinor v g * (1 + a * radicalX v g + b * radicalY v g) := by
  rw [lowerMinor_mul_oppositeRadical, radicalX, radicalY]
  field_simp

private theorem lowerMinor_mul_oppositeRadical_inv_left (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (hL : lowerMinor v g ≠ 0) (hx : radicalX v g ≠ 0) :
    lowerMinor v (g * oppositeRadical v (-(radicalX v g)⁻¹) 0) = 0 := by
  rw [lowerMinor_mul_oppositeRadical_of_ne_zero v g hL, zero_mul, add_zero, neg_mul, inv_mul_cancel₀ hx,
    add_neg_cancel, mul_zero]

private theorem lowerMinor_mul_oppositeRadical_inv_right (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (hL : lowerMinor v g ≠ 0) (hy : radicalY v g ≠ 0) :
    lowerMinor v (g * oppositeRadical v 0 (-(radicalY v g)⁻¹)) = 0 := by
  rw [lowerMinor_mul_oppositeRadical_of_ne_zero v g hL, zero_mul, add_zero, neg_mul, inv_mul_cancel₀ hy,
    add_neg_cancel, mul_zero]

private theorem bottom_mul_oppositeRadical_div (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (h22 : gl3Entry v g 2 2 ≠ 0) :
    gl3Entry v (g * oppositeRadical v (-(gl3Entry v g 2 0 / gl3Entry v g 2 2))
        (-(gl3Entry v g 2 1 / gl3Entry v g 2 2))) 2 0 = 0 ∧
      gl3Entry v (g * oppositeRadical v (-(gl3Entry v g 2 0 / gl3Entry v g 2 2))
        (-(gl3Entry v g 2 1 / gl3Entry v g 2 2))) 2 1 = 0 := by
  obtain ⟨h0, h1, -⟩ := gl3Entry_mul_oppositeRadical v g (-(gl3Entry v g 2 0 / gl3Entry v g 2 2))
    (-(gl3Entry v g 2 1 / gl3Entry v g 2 2))
  rw [h0, h1]
  constructor <;> field_simp <;> ring1

private theorem gl3Entry_mul_center (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (c : (v.adicCompletion ℚ)ˣ)
    (i : Fin 3) :
    gl3Entry v (g * diagonal3 v ![1, 1, c]) i 0 = gl3Entry v g i 0 ∧
      gl3Entry v (g * diagonal3 v ![1, 1, c]) i 1 = gl3Entry v g i 1 ∧
      gl3Entry v (g * diagonal3 v ![1, 1, c]) i 2 = gl3Entry v g i 2 * (c : v.adicCompletion ℚ) := by
  simp only [gl3Entry, Units.val_mul, diagonal3_coe]
  refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.mul_diagonal]

private theorem lowerMinor_mul_center (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (c : (v.adicCompletion ℚ)ˣ) :
    lowerMinor v (g * diagonal3 v ![1, 1, c]) = lowerMinor v g := by
  simp only [lowerMinor, (gl3Entry_mul_center v g c 1).1, (gl3Entry_mul_center v g c 1).2.1,
    (gl3Entry_mul_center v g c 2).1, (gl3Entry_mul_center v g c 2).2.1]

private theorem radicalX_mul_center (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (c : (v.adicCompletion ℚ)ˣ) :
    radicalX v (g * diagonal3 v ![1, 1, c]) = (c : v.adicCompletion ℚ) * radicalX v g := by
  simp only [radicalX, lowerMinor_mul_center, (gl3Entry_mul_center v g c 1).2.1, (gl3Entry_mul_center v g c 1).2.2,
    (gl3Entry_mul_center v g c 2).2.1, (gl3Entry_mul_center v g c 2).2.2]
  rw [← mul_div_assoc]
  congr 1
  ring1

private theorem radicalY_mul_center (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (c : (v.adicCompletion ℚ)ˣ) :
    radicalY v (g * diagonal3 v ![1, 1, c]) = (c : v.adicCompletion ℚ) * radicalY v g := by
  simp only [radicalY, outerMinor, lowerMinor_mul_center, (gl3Entry_mul_center v g c 1).1,
    (gl3Entry_mul_center v g c 1).2.2, (gl3Entry_mul_center v g c 2).1, (gl3Entry_mul_center v g c 2).2.2]
  rw [← mul_div_assoc]
  congr 1
  ring1

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem gl3Entry_mul_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (a b e : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 a b e) i 0 = gl3Entry v g i 0 ∧
      gl3Entry v (g * upperUnipotent3 a b e) i 1 = gl3Entry v g i 1 + gl3Entry v g i 0 * a ∧
      gl3Entry v (g * upperUnipotent3 a b e) i 2 = gl3Entry v g i 2 + gl3Entry v g i 0 * e + gl3Entry v g i 1 * b := by
  simp only [gl3Entry, Units.val_mul, upperUnipotent3_coe]
  refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring1

private theorem lowerMinor_mul_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v)
    (a b e : v.adicCompletion ℚ) : lowerMinor v (g * upperUnipotent3 a b e) = lowerMinor v g := by
  simp only [lowerMinor, (gl3Entry_mul_upperUnipotent3 v g a b e 1).1, (gl3Entry_mul_upperUnipotent3 v g a b e 1).2.1,
    (gl3Entry_mul_upperUnipotent3 v g a b e 2).1, (gl3Entry_mul_upperUnipotent3 v g a b e 2).2.1]
  ring1

private theorem radicalX_mul_radical (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (hL : lowerMinor v g ≠ 0)
    (x y : v.adicCompletion ℚ) : radicalX v (g * upperUnipotent3 0 y x) = radicalX v g + x := by
  have h1 := gl3Entry_mul_upperUnipotent3 v g 0 y x 1
  have h2 := gl3Entry_mul_upperUnipotent3 v g 0 y x 2
  simp only [radicalX, lowerMinor_mul_upperUnipotent3, h1.2.1, h1.2.2, h2.2.1, h2.2.2, mul_zero, add_zero]
  simp only [lowerMinor] at hL ⊢
  field_simp
  ring1

private theorem radicalY_mul_radical (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (hL : lowerMinor v g ≠ 0)
    (x y : v.adicCompletion ℚ) : radicalY v (g * upperUnipotent3 0 y x) = radicalY v g + y := by
  have h1 := gl3Entry_mul_upperUnipotent3 v g 0 y x 1
  have h2 := gl3Entry_mul_upperUnipotent3 v g 0 y x 2
  have houter : outerMinor v (g * upperUnipotent3 0 y x) = outerMinor v g + y * lowerMinor v g := by
    simp only [outerMinor, lowerMinor, h1.1, h1.2.2, h2.1, h2.2.2]
    ring1
  rw [radicalY, radicalY, lowerMinor_mul_upperUnipotent3, houter, add_div, mul_div_assoc, div_self hL, mul_one]

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem level_radical (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) {x y : v.adicCompletion ℚ}
    (hx : Valued.v x ≤ WithZero.exp (-(n : ℤ))) (hy : Valued.v y ≤ WithZero.exp (-(n : ℤ))) (i j : Fin 3) :
    Valued.v (gl3Entry v (upperUnipotent3 0 y x) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
      ≤ WithZero.exp (-(n : ℤ)) := by
  fin_cases i <;> fin_cases j <;> simp [gl3Entry, upperUnipotent3_coe]
  · simpa using hx
  · simpa using hy

private theorem level_oppositeRadical (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) {a b : v.adicCompletion ℚ}
    (ha : Valued.v a ≤ WithZero.exp (-(n : ℤ))) (hb : Valued.v b ≤ WithZero.exp (-(n : ℤ))) (i j : Fin 3) :
    Valued.v (gl3Entry v (oppositeRadical v a b) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
      ≤ WithZero.exp (-(n : ℤ)) := by
  fin_cases i <;> fin_cases j <;> simp [gl3Entry, oppositeRadical_coe]
  · simpa using ha
  · simpa using hb

private theorem valued_neg_inv_le (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) {x : v.adicCompletion ℚ}
    (hx : WithZero.exp (n : ℤ) ≤ Valued.v x) : Valued.v (-x⁻¹) ≤ WithZero.exp (-(n : ℤ)) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  rw [Valuation.map_neg, map_inv₀, WithZero.exp_neg]
  exact inv_anti₀ WithZero.exp_pos hx

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

section Indicator

open scoped Topology in

private theorem isLocallyConstant_indicator {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    (hf : IsLocallyConstant f) (S : Set X) (hS : ∀ x, f x ≠ 0 → ∀ᶠ y in 𝓝 x, (y ∈ S ↔ x ∈ S)) :
    IsLocallyConstant (S.indicator f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : f x = 0
  · filter_upwards [hf.eventually_eq x] with y hy
    rw [Set.indicator_apply_eq_zero.mpr fun _ => hy.trans hx, Set.indicator_apply_eq_zero.mpr fun _ => hx]
  · filter_upwards [hf.eventually_eq x, hS x hx] with y hy hyS
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem (hyS.mpr hxS), hy]
    · rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem fun h => hxS (hyS.mp h)]

private theorem indicator_mem_principalSeries3 (v : HeightOneSpectrum (𝓞 ℚ))
    {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (S : Set (LocalGL3 v)) (hlc : IsLocallyConstant (S.indicator f))
    (hSn : ∀ (x y z : v.adicCompletion ℚ) (g : LocalGL3 v), upperUnipotent3 x y z * g ∈ S ↔ g ∈ S)
    (hSd : ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v), diagonal3 v a * g ∈ S ↔ g ∈ S) :
    S.indicator f ∈ principalSeries3 v χ := by
  obtain ⟨-, hfn, hft⟩ := hf
  refine ⟨hlc, fun x y z g => ?_, fun a g => ?_⟩
  · by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem ((hSn x y z g).mpr hg), Set.indicator_of_mem hg]
      exact hfn x y z g
    · rw [Set.indicator_of_notMem fun h => hg ((hSn x y z g).mp h), Set.indicator_of_notMem hg]
  · by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem ((hSd a g).mpr hg), Set.indicator_of_mem hg]
      exact hft a g
    · rw [Set.indicator_of_notMem fun h => hg ((hSd a g).mp h), Set.indicator_of_notMem hg, mul_zero]

private theorem rightTranslate_indicator {v : HeightOneSpectrum (𝓞 ℚ)} (f : LocalGL3 v → ℂ) (S : Set (LocalGL3 v))
    (k : LocalGL3 v) :
    gl3AmbientRightTranslate (R := ℂ) k (S.indicator f) =
      {g | g * k ∈ S}.indicator (gl3AmbientRightTranslate (R := ℂ) k f) := by
  funext g
  show S.indicator f (g * k) = {g | g * k ∈ S}.indicator (fun h => f (h * k)) g
  by_cases hg : g * k ∈ S
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (show g ∈ {g | g * k ∈ S} from hg)]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (show g ∉ {g | g * k ∈ S} from hg)]

end Indicator
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

section LevelBall

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem exists_valued_eq_exp (m : ℤ) : ∃ c : v.adicCompletion ℚ, Valued.v c = WithZero.exp m := by
  refine ⟨((NumberField.AdelicLevel.uniformizerUnit ℚ v ^ (-m) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), ?_⟩
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

open scoped Topology in

private theorem isClopen_valued_le_exp (m : ℤ) :
    IsClopen {y : v.adicCompletion ℚ | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := exists_valued_eq_exp v m
  have hc0 : c ≠ 0 := fun h => by
    rw [h, Valuation.map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  constructor
  · rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx' : WithZero.exp m < Valued.v x := not_le.mp hx
    have hx0 : x ≠ 0 := fun h => by
      rw [h, Valuation.map_zero] at hx'
      exact (not_lt.mpr zero_le') hx'
    filter_upwards [eventually_valued_eq v hx0] with y hy
    rw [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, hy]
    exact hx'
  · rw [isOpen_iff_mem_nhds]
    intro x hx
    have ht : Filter.Tendsto (fun y : v.adicCompletion ℚ => y - x) (𝓝 x) (𝓝 0) := by
      simpa only [sub_self] using (continuous_sub_right x).tendsto x
    filter_upwards [ht.eventually (eventually_valued_lt v hc0)] with y hy
    have hsum : y = y - x + x := (sub_add_cancel y x).symm
    show Valued.v y ≤ WithZero.exp m
    rw [hsum]
    exact (Valued.v.map_add (y - x) x).trans (max_le (hy.le.trans hc.le) hx)

open scoped Topology in

private theorem eventually_valued_sub_le_iff {g : LocalGL3 v} {c : LocalGL3 v → v.adicCompletion ℚ}
    (hc : ContinuousAt c g) (p : v.adicCompletion ℚ) (m : ℤ) :
    ∀ᶠ h in 𝓝 g, (Valued.v (c h - p) ≤ WithZero.exp m ↔ Valued.v (c g - p) ≤ WithZero.exp m) :=
  (hc.sub continuousAt_const).tendsto.eventually (eventually_mem_iff_of_isClopen v (isClopen_valued_le_exp v m) _)

end LevelBall
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

section OpenPiece

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem continuousAt_radicalX {g : LocalGL3 v} (hL : lowerMinor v g ≠ 0) : ContinuousAt (radicalX v) g := by
  show ContinuousAt (fun h => (gl3Entry v h 1 2 * gl3Entry v h 2 1 - gl3Entry v h 1 1 * gl3Entry v h 2 2) /
    lowerMinor v h) g
  exact ((((continuous_gl3Entry v 1 2).mul (continuous_gl3Entry v 2 1)).sub
    ((continuous_gl3Entry v 1 1).mul (continuous_gl3Entry v 2 2))).continuousAt).div
    (continuous_lowerMinor v).continuousAt hL

private theorem continuousAt_radicalY {g : LocalGL3 v} (hL : lowerMinor v g ≠ 0) : ContinuousAt (radicalY v) g := by
  show ContinuousAt (fun h => outerMinor v h / lowerMinor v h) g
  exact (continuous_outerMinor v).continuousAt.div (continuous_lowerMinor v).continuousAt hL

open scoped Topology in

private theorem eventually_disc_iff {g : LocalGL3 v} (hL : lowerMinor v g ≠ 0) :
    ∀ᶠ h in 𝓝 g, ((Valued.v (gl3Entry v h 2 0) ≤ Valued.v (gl3Entry v h 2 1)) ↔
      (Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1))) := by
  by_cases h21 : gl3Entry v g 2 1 = 0
  ·
    have h20 : gl3Entry v g 2 0 ≠ 0 := by
      intro h20
      apply hL
      rw [lowerMinor, h20, h21]
      ring
    have hfalse : ¬(Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)) := by
      rw [h21, Valuation.map_zero]
      exact not_le.mpr (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr h20))
    have ht : Filter.Tendsto (fun h : LocalGL3 v => gl3Entry v h 2 1) (𝓝 g) (𝓝 0) := by
      simpa [h21] using (continuous_gl3Entry v 2 1).tendsto g
    filter_upwards [((continuous_gl3Entry v 2 0).tendsto g).eventually (eventually_valued_eq v h20),
      ht.eventually (eventually_valued_lt v h20)] with h hh20 hh21
    refine iff_of_false ?_ hfalse
    rw [hh20]
    exact not_le.mpr hh21
  · by_cases h20 : gl3Entry v g 2 0 = 0
    ·
      have htrue : Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1) := by
        rw [h20, Valuation.map_zero]
        exact zero_le'
      have ht : Filter.Tendsto (fun h : LocalGL3 v => gl3Entry v h 2 0) (𝓝 g) (𝓝 0) := by
        simpa [h20] using (continuous_gl3Entry v 2 0).tendsto g
      filter_upwards [((continuous_gl3Entry v 2 1).tendsto g).eventually (eventually_valued_eq v h21),
        ht.eventually (eventually_valued_lt v h21)] with h hh21 hh20
      refine iff_of_true ?_ htrue
      rw [hh21]
      exact hh20.le
    ·
      filter_upwards [((continuous_gl3Entry v 2 0).tendsto g).eventually (eventually_valued_eq v h20),
        ((continuous_gl3Entry v 2 1).tendsto g).eventually (eventually_valued_eq v h21)] with h hh20 hh21
      rw [hh20, hh21]

private noncomputable def cutFirst (n : ℕ) (p q : v.adicCompletion ℚ) : Set (LocalGL3 v) :=
  {g | lowerMinor v g ≠ 0 ∧ Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1) ∧
    Valued.v (radicalX v g - p) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (radicalY v g - q) ≤ WithZero.exp (-(n : ℤ))}

private noncomputable def cutZeroth (n : ℕ) (p q : v.adicCompletion ℚ) : Set (LocalGL3 v) :=
  {g | lowerMinor v g ≠ 0 ∧ ¬(Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)) ∧
    Valued.v (radicalX v g - p) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (radicalY v g - q) ≤ WithZero.exp (-(n : ℤ))}

open scoped Topology in

private theorem eventually_mem_cut_iff (n : ℕ) (p q : v.adicCompletion ℚ) {g : LocalGL3 v}
    (hL : lowerMinor v g ≠ 0) :
    (∀ᶠ h in 𝓝 g, (h ∈ cutFirst v n p q ↔ g ∈ cutFirst v n p q)) ∧
      ∀ᶠ h in 𝓝 g, (h ∈ cutZeroth v n p q ↔ g ∈ cutZeroth v n p q) := by
  have hLev : ∀ᶠ h in 𝓝 g, lowerMinor v h ≠ 0 := (continuous_lowerMinor v).continuousAt.eventually_ne hL
  have hX := eventually_valued_sub_le_iff v (continuousAt_radicalX v hL) p (-(n : ℤ))
  have hY := eventually_valued_sub_le_iff v (continuousAt_radicalY v hL) q (-(n : ℤ))
  have hD := eventually_disc_iff v hL
  constructor
  · filter_upwards [hLev, hX, hY, hD] with h hhL hhX hhY hhD
    simp only [cutFirst, Set.mem_setOf_eq]
    exact and_congr (iff_of_true hhL hL) (and_congr hhD (and_congr hhX hhY))
  · filter_upwards [hLev, hX, hY, hD] with h hhL hhX hhY hhD
    simp only [cutZeroth, Set.mem_setOf_eq]
    exact and_congr (iff_of_true hhL hL) (and_congr (not_congr hhD) (and_congr hhX hhY))

private theorem isLocallyConstant_indicator_cut {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (hvan : ∀ g, lowerMinor v g = 0 → f g = 0) (n : ℕ)
    (p q : v.adicCompletion ℚ) :
    IsLocallyConstant ((cutFirst v n p q).indicator f) ∧ IsLocallyConstant ((cutZeroth v n p q).indicator f) := by
  obtain ⟨hf1, -, -⟩ := hf
  have hsupp : ∀ g, f g ≠ 0 → lowerMinor v g ≠ 0 := fun g hg hL => hg (hvan g hL)
  exact ⟨isLocallyConstant_indicator hf1 _ fun g hg => (eventually_mem_cut_iff v n p q (hsupp g hg)).1,
    isLocallyConstant_indicator hf1 _ fun g hg => (eventually_mem_cut_iff v n p q (hsupp g hg)).2⟩

end OpenPiece
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem valued_mul_le_valued_mul_iff (v : HeightOneSpectrum (𝓞 ℚ)) {c : v.adicCompletion ℚ} (hc : c ≠ 0)
    (x y : v.adicCompletion ℚ) :
    Valued.v (c * x) ≤ Valued.v (c * y) ↔ Valued.v x ≤ Valued.v y := by
  rw [map_mul, map_mul]
  exact mul_le_mul_iff_right₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc))

private theorem cutFirst_upperUnipotent3_mul_iff (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) (n : ℕ) (p q : v.adicCompletion ℚ) :
    upperUnipotent3 x y z * g ∈ cutFirst v n p q ↔ g ∈ cutFirst v n p q := by
  simp only [cutFirst, Set.mem_setOf_eq, lowerMinor_upperUnipotent3_mul, gl3Entry_upperUnipotent3_mul_two,
    radicalX_upperUnipotent3_mul, radicalY_upperUnipotent3_mul]

private theorem cutZeroth_upperUnipotent3_mul_iff (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) (n : ℕ) (p q : v.adicCompletion ℚ) :
    upperUnipotent3 x y z * g ∈ cutZeroth v n p q ↔ g ∈ cutZeroth v n p q := by
  simp only [cutZeroth, Set.mem_setOf_eq, lowerMinor_upperUnipotent3_mul, gl3Entry_upperUnipotent3_mul_two,
    radicalX_upperUnipotent3_mul, radicalY_upperUnipotent3_mul]

private theorem cutFirst_diagonal3_mul_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) (n : ℕ) (p q : v.adicCompletion ℚ) :
    diagonal3 v a * g ∈ cutFirst v n p q ↔ g ∈ cutFirst v n p q := by
  simp only [cutFirst, Set.mem_setOf_eq, lowerMinor_diagonal3_mul, gl3Entry_diagonal3_mul,
    radicalX_diagonal3_mul, radicalY_diagonal3_mul]
  rw [valued_mul_le_valued_mul_iff v (a 2).ne_zero]
  simp only [ne_eq, mul_eq_zero, (a 1).ne_zero, (a 2).ne_zero, or_self, false_or]

private theorem cutZeroth_diagonal3_mul_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) (n : ℕ) (p q : v.adicCompletion ℚ) :
    diagonal3 v a * g ∈ cutZeroth v n p q ↔ g ∈ cutZeroth v n p q := by
  simp only [cutZeroth, Set.mem_setOf_eq, lowerMinor_diagonal3_mul, gl3Entry_diagonal3_mul,
    radicalX_diagonal3_mul, radicalY_diagonal3_mul]
  rw [valued_mul_le_valued_mul_iff v (a 2).ne_zero]
  simp only [ne_eq, mul_eq_zero, (a 1).ne_zero, (a 2).ne_zero, or_self, false_or]

private theorem indicator_cut_mem (v : HeightOneSpectrum (𝓞 ℚ))
    {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (hvan : ∀ g, lowerMinor v g = 0 → f g = 0) (n : ℕ)
    (p q : v.adicCompletion ℚ) :
    (cutFirst v n p q).indicator f ∈ principalSeries3 v χ ∧
      (cutZeroth v n p q).indicator f ∈ principalSeries3 v χ := by
  obtain ⟨h1, h2⟩ := isLocallyConstant_indicator_cut v hf hvan n p q
  exact ⟨indicator_mem_principalSeries3 v hf _ h1
      (fun x y z g => cutFirst_upperUnipotent3_mul_iff v x y z g n p q)
      (fun a g => cutFirst_diagonal3_mul_iff v a g n p q),
    indicator_mem_principalSeries3 v hf _ h2
      (fun x y z g => cutZeroth_upperUnipotent3_mul_iff v x y z g n p q)
      (fun a g => cutZeroth_diagonal3_mul_iff v a g n p q)⟩

private theorem indicator_cut_vanish (v : HeightOneSpectrum (𝓞 ℚ))
    {f : LocalGL3 v → ℂ} (hvan : ∀ g, lowerMinor v g = 0 → f g = 0) (n : ℕ)
    (p q : v.adicCompletion ℚ) (g : LocalGL3 v) (hL : lowerMinor v g = 0) :
    (cutFirst v n p q).indicator f g = 0 ∧ (cutZeroth v n p q).indicator f g = 0 :=
  ⟨Set.indicator_apply_eq_zero.mpr fun _ => hvan g hL, Set.indicator_apply_eq_zero.mpr fun _ => hvan g hL⟩

private noncomputable def midCutFirst (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (p : v.adicCompletion ℚ)
    : Set (LocalGL3 v) :=
  {g | Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1) ∧
    Valued.v (gl3Entry v g 2 2 / gl3Entry v g 2 1 - p) ≤ WithZero.exp (-(n : ℤ))}

private noncomputable def midCutZeroth (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (p : v.adicCompletion ℚ)
    : Set (LocalGL3 v) :=
  {g | ¬(Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)) ∧
    Valued.v (gl3Entry v g 2 2 / gl3Entry v g 2 0 - p) ≤ WithZero.exp (-(n : ℤ))}

private theorem midCutFirst_upperUnipotent3_mul_iff (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) (n : ℕ) (p : v.adicCompletion ℚ) :
    upperUnipotent3 x y z * g ∈ midCutFirst v n p ↔ g ∈ midCutFirst v n p := by
  simp only [midCutFirst, Set.mem_setOf_eq, gl3Entry_upperUnipotent3_mul_two]

private theorem midCutZeroth_upperUnipotent3_mul_iff (v : HeightOneSpectrum (𝓞 ℚ)) (x y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) (n : ℕ) (p : v.adicCompletion ℚ) :
    upperUnipotent3 x y z * g ∈ midCutZeroth v n p ↔ g ∈ midCutZeroth v n p := by
  simp only [midCutZeroth, Set.mem_setOf_eq, gl3Entry_upperUnipotent3_mul_two]

private theorem midCutFirst_diagonal3_mul_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) (n : ℕ) (p : v.adicCompletion ℚ) :
    diagonal3 v a * g ∈ midCutFirst v n p ↔ g ∈ midCutFirst v n p := by
  simp only [midCutFirst, Set.mem_setOf_eq, gl3Entry_diagonal3_mul]
  rw [valued_mul_le_valued_mul_iff v (a 2).ne_zero, mul_div_mul_left _ _ (a 2).ne_zero]

private theorem midCutZeroth_diagonal3_mul_iff (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) (n : ℕ) (p : v.adicCompletion ℚ) :
    diagonal3 v a * g ∈ midCutZeroth v n p ↔ g ∈ midCutZeroth v n p := by
  simp only [midCutZeroth, Set.mem_setOf_eq, gl3Entry_diagonal3_mul]
  rw [valued_mul_le_valued_mul_iff v (a 2).ne_zero, mul_div_mul_left _ _ (a 2).ne_zero]

open scoped Topology in

private theorem eventually_disc_iff_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) {g : LocalGL3 v}
    (hg : ¬(gl3Entry v g 2 0 = 0 ∧ gl3Entry v g 2 1 = 0)) :
    ∀ᶠ h in 𝓝 g, ((Valued.v (gl3Entry v h 2 0) ≤ Valued.v (gl3Entry v h 2 1)) ↔
      (Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1))) := by
  by_cases h21 : gl3Entry v g 2 1 = 0
  · have h20 : gl3Entry v g 2 0 ≠ 0 := fun h20 => hg ⟨h20, h21⟩
    have hfalse : ¬(Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)) := by
      rw [h21, Valuation.map_zero]
      exact not_le.mpr (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr h20))
    have ht : Filter.Tendsto (fun h : LocalGL3 v => gl3Entry v h 2 1) (𝓝 g) (𝓝 0) := by
      simpa [h21] using (continuous_gl3Entry v 2 1).tendsto g
    filter_upwards [((continuous_gl3Entry v 2 0).tendsto g).eventually (eventually_valued_eq v h20),
      ht.eventually (eventually_valued_lt v h20)] with h hh20 hh21
    refine iff_of_false ?_ hfalse
    rw [hh20]
    exact not_le.mpr hh21
  · by_cases h20 : gl3Entry v g 2 0 = 0
    · have htrue : Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1) := by
        rw [h20, Valuation.map_zero]
        exact zero_le'
      have ht : Filter.Tendsto (fun h : LocalGL3 v => gl3Entry v h 2 0) (𝓝 g) (𝓝 0) := by
        simpa [h20] using (continuous_gl3Entry v 2 0).tendsto g
      filter_upwards [((continuous_gl3Entry v 2 1).tendsto g).eventually (eventually_valued_eq v h21),
        ht.eventually (eventually_valued_lt v h21)] with h hh21 hh20
      refine iff_of_true ?_ htrue
      rw [hh21]
      exact hh20.le
    · filter_upwards [((continuous_gl3Entry v 2 0).tendsto g).eventually (eventually_valued_eq v h20),
        ((continuous_gl3Entry v 2 1).tendsto g).eventually (eventually_valued_eq v h21)] with h hh20 hh21
      rw [hh20, hh21]

open scoped Topology in

private theorem eventually_mem_midCut_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (p : v.adicCompletion ℚ)
    {g : LocalGL3 v}
    (hg : ¬(gl3Entry v g 2 0 = 0 ∧ gl3Entry v g 2 1 = 0)) :
    (∀ᶠ h in 𝓝 g, (h ∈ midCutFirst v n p ↔ g ∈ midCutFirst v n p)) ∧
      ∀ᶠ h in 𝓝 g, (h ∈ midCutZeroth v n p ↔ g ∈ midCutZeroth v n p) := by
  have hD := eventually_disc_iff_of_ne v hg
  by_cases hd : Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)
  ·
    have h21 : gl3Entry v g 2 1 ≠ 0 := by
      intro h21
      apply hg
      refine ⟨?_, h21⟩
      rw [h21, Valuation.map_zero] at hd
      exact (Valuation.zero_iff _).mp (le_antisymm hd zero_le')
    have hr := eventually_valued_sub_le_iff v
      ((continuous_gl3Entry v 2 2).continuousAt.div (continuous_gl3Entry v 2 1).continuousAt h21) p
      (-(n : ℤ))
    constructor
    · filter_upwards [hD, hr] with h hhD hhr
      simp only [midCutFirst, Set.mem_setOf_eq]
      exact and_congr hhD hhr
    · filter_upwards [hD] with h hhD
      simp only [midCutZeroth, Set.mem_setOf_eq]
      exact iff_of_false (fun hm => hm.1 (hhD.mpr hd)) (fun hm => hm.1 hd)
  ·
    have h20 : gl3Entry v g 2 0 ≠ 0 := by
      intro h20
      apply hd
      rw [h20, Valuation.map_zero]
      exact zero_le'
    have hr := eventually_valued_sub_le_iff v
      ((continuous_gl3Entry v 2 2).continuousAt.div (continuous_gl3Entry v 2 0).continuousAt h20) p
      (-(n : ℤ))
    constructor
    · filter_upwards [hD] with h hhD
      simp only [midCutFirst, Set.mem_setOf_eq]
      exact iff_of_false (fun hm => hd (hhD.mp hm.1)) (fun hm => hd hm.1)
    · filter_upwards [hD, hr] with h hhD hhr
      simp only [midCutZeroth, Set.mem_setOf_eq]
      exact and_congr (not_congr hhD) hhr

private theorem indicator_midCut_mem (v : HeightOneSpectrum (𝓞 ℚ))
    {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (hP : ∀ g, gl3Entry v g 2 0 = 0 → gl3Entry v g 2 1 = 0 → f g = 0)
    (n : ℕ)
    (p : v.adicCompletion ℚ) :
    (midCutFirst v n p).indicator f ∈ principalSeries3 v χ ∧
      (midCutZeroth v n p).indicator f ∈ principalSeries3 v χ := by
  have hf' := hf
  obtain ⟨hf1, -, -⟩ := hf'
  have hsupp : ∀ g, f g ≠ 0 → ¬(gl3Entry v g 2 0 = 0 ∧ gl3Entry v g 2 1 = 0) :=
    fun g hg h => hg (hP g h.1 h.2)
  exact ⟨indicator_mem_principalSeries3 v hf _
      (isLocallyConstant_indicator hf1 _ fun g hg => (eventually_mem_midCut_iff v n p (hsupp g hg)).1)
      (fun x y z g => midCutFirst_upperUnipotent3_mul_iff v x y z g n p)
      (fun a g => midCutFirst_diagonal3_mul_iff v a g n p),
    indicator_mem_principalSeries3 v hf _
      (isLocallyConstant_indicator hf1 _ fun g hg => (eventually_mem_midCut_iff v n p (hsupp g hg)).2)
      (fun x y z g => midCutZeroth_upperUnipotent3_mul_iff v x y z g n p)
      (fun a g => midCutZeroth_diagonal3_mul_iff v a g n p)⟩

private theorem indicator_midCut_vanish (v : HeightOneSpectrum (𝓞 ℚ)) {f : LocalGL3 v → ℂ}
    (hP : ∀ g, gl3Entry v g 2 0 = 0 → gl3Entry v g 2 1 = 0 → f g = 0) (n : ℕ) (p : v.adicCompletion ℚ)
    (g : LocalGL3 v) (h0 : gl3Entry v g 2 0 = 0) (h1 : gl3Entry v g 2 1 = 0) :
    (midCutFirst v n p).indicator f g = 0 ∧ (midCutZeroth v n p).indicator f g = 0 :=
  ⟨Set.indicator_apply_eq_zero.mpr fun _ => hP g h0 h1, Set.indicator_apply_eq_zero.mpr fun _ => hP g h0 h1⟩

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

section Engine

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem indicator_center_eq_sum_of_chart (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) {u : LocalGL3 v → ℂ}
    (hu : u ∈ principalSeries3 v ![θ, θ, θ']) (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u)
    (c : (v.adicCompletion ℚ)ˣ) (hc : Valued.v (c : v.adicCompletion ℚ) ≤ 1) (T : Finset (v.adicCompletion ℚ))
    (hTsub : ∀ r ∈ T, r ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))))
    (hT : ∀ a ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))),
      ∃ r ∈ T, a - r ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (hT' : ∀ r ∈ T, ∀ r' ∈ T, r - r' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) → r = r')
    (S : Set (LocalGL3 v)) (D : v.adicCompletion ℚ → v.adicCompletion ℚ → Prop) (p q : v.adicCompletion ℚ)
    (hS : ∀ g' : LocalGL3 v, g' ∈ S ↔ lowerMinor v g' ≠ 0 ∧ D (gl3Entry v g' 2 0) (gl3Entry v g' 2 1) ∧
      Valued.v (radicalX v g' - p) ≤ WithZero.exp (-(n : ℤ)) ∧
      Valued.v (radicalY v g' - q) ≤ WithZero.exp (-(n : ℤ)))
    (g : LocalGL3 v) (hL : lowerMinor v g ≠ 0) (hD : D (gl3Entry v g 2 0) (gl3Entry v g 2 1))
    (a₀ b₀ e₀ : v.adicCompletion ℚ) (d : Fin 3 → (v.adicCompletion ℚ)ˣ) (B : LocalGL3 v)
    (x y : v.adicCompletion ℚ)
    (hg : g = upperUnipotent3 a₀ b₀ e₀ * (diagonal3 v d * (B * upperUnipotent3 0 y x)))
    (hB : B * diagonal3 v ![1, 1, c] = diagonal3 v ![c, 1, 1] * B)
    (hsec : ∀ ξ η : v.adicCompletion ℚ, radicalX v (B * upperUnipotent3 0 η ξ) = ξ ∧
      radicalY v (B * upperUnipotent3 0 η ξ) = η) :
    S.indicator u (g * diagonal3 v ![1, 1, c]) =
      (torusChar3 v ![θ, θ, θ'] ![c, 1, 1] * halfModulus3 v ![c, 1, 1]) *
        ∑ r ∈ T, ∑ s ∈ T, S.indicator u
          (g * upperUnipotent3 0 (q - (c : v.adicCompletion ℚ)⁻¹ * q - s)
            (p - (c : v.adicCompletion ℚ)⁻¹ * p - r)) := by

  have hc0 : (c : v.adicCompletion ℚ) ≠ 0 := c.ne_zero
  set L := LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ))
  set P : v.adicCompletion ℚ → v.adicCompletion ℚ → LocalGL3 v := fun ξ η => B * upperUnipotent3 0 η ξ with hP

  have hxg : radicalX v g = x := by
    rw [hg, radicalX_upperUnipotent3_mul, radicalX_diagonal3_mul, (hsec x y).1]
  have hyg : radicalY v g = y := by
    rw [hg, radicalY_upperUnipotent3_mul, radicalY_diagonal3_mul, (hsec x y).2]

  have hval_z : u (g * diagonal3 v ![1, 1, c]) =
      (torusChar3 v ![θ, θ, θ'] d * halfModulus3 v d) *
        ((torusChar3 v ![θ, θ, θ'] ![c, 1, 1] * halfModulus3 v ![c, 1, 1]) *
          u (P ((c : v.adicCompletion ℚ) * x) ((c : v.adicCompletion ℚ) * y))) := by
    have e : g * diagonal3 v ![1, 1, c] = upperUnipotent3 a₀ b₀ e₀ * (diagonal3 v d * (diagonal3 v ![c, 1, 1] *
        P ((c : v.adicCompletion ℚ) * x) ((c : v.adicCompletion ℚ) * y))) := by
      rw [hg]
      simp only [hP, mul_assoc, radical_mul_center]
      rw [← mul_assoc B, hB, mul_assoc]
    rw [e, apply_upperUnipotent3_mul_of_mem_principalSeries3 hu, apply_diagonal3_mul_of_mem_principalSeries3 hu,
      apply_diagonal3_mul_of_mem_principalSeries3 hu]
  have hval_n : ∀ α β : v.adicCompletion ℚ,
      u (g * upperUnipotent3 0 β α) = (torusChar3 v ![θ, θ, θ'] d * halfModulus3 v d) * u (P (x + α) (y + β)) := by
    intro α β
    have e : g * upperUnipotent3 0 β α = upperUnipotent3 a₀ b₀ e₀ * (diagonal3 v d * P (x + α) (y + β)) := by
      rw [hg]
      simp only [hP, mul_assoc, radical_mul]
    rw [e, apply_upperUnipotent3_mul_of_mem_principalSeries3 hu, apply_diagonal3_mul_of_mem_principalSeries3 hu]

  have hmem_z : g * diagonal3 v ![1, 1, c] ∈ S ↔
      (c : v.adicCompletion ℚ) * x - p ∈ L ∧ (c : v.adicCompletion ℚ) * y - q ∈ L := by
    rw [hS, lowerMinor_mul_center, (gl3Entry_mul_center v g c 2).1, (gl3Entry_mul_center v g c 2).2.1,
      radicalX_mul_center, radicalY_mul_center, hxg, hyg]
    exact ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨hL, hD, h.1, h.2⟩⟩
  have hmem_n : ∀ α β : v.adicCompletion ℚ, g * upperUnipotent3 0 β α ∈ S ↔
      x + α - p ∈ L ∧ y + β - q ∈ L := by
    intro α β
    rw [hS, lowerMinor_mul_upperUnipotent3, (gl3Entry_mul_upperUnipotent3 v g 0 β α 2).1,
      (gl3Entry_mul_upperUnipotent3 v g 0 β α 2).2.1, mul_zero, add_zero, radicalX_mul_radical v g hL,
      radicalY_mul_radical v g hL, hxg, hyg]
    exact ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨hL, hD, h.1, h.2⟩⟩

  have hterm : ∀ r ∈ T, ∀ s ∈ T,
      S.indicator u (g * upperUnipotent3 0 (q - (c : v.adicCompletion ℚ)⁻¹ * q - s)
        (p - (c : v.adicCompletion ℚ)⁻¹ * p - r)) =
      LevelLattice.cosetPairIndicator L ((c : v.adicCompletion ℚ)⁻¹ * p + r) ((c : v.adicCompletion ℚ)⁻¹ * q + s) x y
        * ((torusChar3 v ![θ, θ, θ'] d * halfModulus3 v d) *
          u (P ((c : v.adicCompletion ℚ) * x) ((c : v.adicCompletion ℚ) * y))) := by
    intro r hr s hs
    have hshape : x + (p - (c : v.adicCompletion ℚ)⁻¹ * p - r) - p = x - ((c : v.adicCompletion ℚ)⁻¹ * p + r) ∧
        y + (q - (c : v.adicCompletion ℚ)⁻¹ * q - s) - q = y - ((c : v.adicCompletion ℚ)⁻¹ * q + s) := by
      constructor <;> ring
    by_cases hcond : x - ((c : v.adicCompletion ℚ)⁻¹ * p + r) ∈ L ∧ y - ((c : v.adicCompletion ℚ)⁻¹ * q + s) ∈ L
    ·
      have hmem : g * upperUnipotent3 0 (q - (c : v.adicCompletion ℚ)⁻¹ * q - s)
          (p - (c : v.adicCompletion ℚ)⁻¹ * p - r) ∈ S := by
        rw [hmem_n, hshape.1, hshape.2]
        exact hcond
      rw [Set.indicator_of_mem hmem, LevelLattice.cosetPairIndicator_of_mem hcond.1 hcond.2, one_mul, hval_n]
      congr 1

      set δ₁ := (c : v.adicCompletion ℚ) * x - (x + (p - (c : v.adicCompletion ℚ)⁻¹ * p - r)) with hδ₁
      set δ₂ := (c : v.adicCompletion ℚ) * y - (y + (q - (c : v.adicCompletion ℚ)⁻¹ * q - s)) with hδ₂
      have hδ₁L : δ₁ ∈ L := by
        have e : δ₁ = (c : v.adicCompletion ℚ) * (x - ((c : v.adicCompletion ℚ)⁻¹ * p + r)) +
            (c : v.adicCompletion ℚ) * r - (x - ((c : v.adicCompletion ℚ)⁻¹ * p + r)) := by
          rw [hδ₁, mul_sub, mul_add, mul_inv_cancel_left₀ hc0]
          ring
        rw [e]
        exact L.sub_mem (L.add_mem (LevelLattice.mem_dilate.mp (LevelLattice.levelBall_le_dilate hc hcond.1))
          (LevelLattice.mem_dilate.mp (hTsub r hr))) hcond.1
      have hδ₂L : δ₂ ∈ L := by
        have e : δ₂ = (c : v.adicCompletion ℚ) * (y - ((c : v.adicCompletion ℚ)⁻¹ * q + s)) +
            (c : v.adicCompletion ℚ) * s - (y - ((c : v.adicCompletion ℚ)⁻¹ * q + s)) := by
          rw [hδ₂, mul_sub, mul_add, mul_inv_cancel_left₀ hc0]
          ring
        rw [e]
        exact L.sub_mem (L.add_mem (LevelLattice.mem_dilate.mp (LevelLattice.levelBall_le_dilate hc hcond.2))
          (LevelLattice.mem_dilate.mp (hTsub s hs))) hcond.2
      have hpt : P ((c : v.adicCompletion ℚ) * x) ((c : v.adicCompletion ℚ) * y) =
          P (x + (p - (c : v.adicCompletion ℚ)⁻¹ * p - r)) (y + (q - (c : v.adicCompletion ℚ)⁻¹ * q - s)) *
            upperUnipotent3 0 δ₂ δ₁ := by
        simp only [hP, mul_assoc, radical_mul]
        congr 2 <;> simp only [hδ₁, hδ₂] <;> ring
      have hk := congrFun (hlev (upperUnipotent3 0 δ₂ δ₁)
        (level_radical v n (LevelLattice.mem_levelBall.mp hδ₁L) (LevelLattice.mem_levelBall.mp hδ₂L)))
        (P (x + (p - (c : v.adicCompletion ℚ)⁻¹ * p - r)) (y + (q - (c : v.adicCompletion ℚ)⁻¹ * q - s)))
      rw [gl3AmbientRightTranslate_apply] at hk
      rw [hpt, hk]
    · have hnot : g * upperUnipotent3 0 (q - (c : v.adicCompletion ℚ)⁻¹ * q - s)
          (p - (c : v.adicCompletion ℚ)⁻¹ * p - r) ∉ S := by
        rw [hmem_n, hshape.1, hshape.2]
        exact hcond
      rw [Set.indicator_of_notMem hnot, LevelLattice.cosetPairIndicator_of_not hcond, zero_mul]

  have hleft : S.indicator u (g * diagonal3 v ![1, 1, c]) =
      LevelLattice.cosetPairIndicator L p q ((c : v.adicCompletion ℚ) * x) ((c : v.adicCompletion ℚ) * y) *
        ((torusChar3 v ![θ, θ, θ'] d * halfModulus3 v d) *
        ((torusChar3 v ![θ, θ, θ'] ![c, 1, 1] * halfModulus3 v ![c, 1, 1]) *
          u (P ((c : v.adicCompletion ℚ) * x) ((c : v.adicCompletion ℚ) * y)))) := by
    by_cases hcond : (c : v.adicCompletion ℚ) * x - p ∈ L ∧ (c : v.adicCompletion ℚ) * y - q ∈ L
    · rw [Set.indicator_of_mem (hmem_z.mpr hcond), LevelLattice.cosetPairIndicator_of_mem hcond.1 hcond.2, one_mul,
        hval_z]
    · rw [Set.indicator_of_notMem fun h => hcond (hmem_z.mp h), LevelLattice.cosetPairIndicator_of_not hcond,
        zero_mul]

  have hsum := congrFun (congrFun (LevelLattice.cosetPairIndicator_mul L (c : v.adicCompletion ℚ) hc0
    (LevelLattice.levelBall_le_dilate hc) T hTsub hT hT' p q) x) y
  beta_reduce at hsum

  rw [hleft, hsum, Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun s hs => hterm r hr s hs]
  simp only [← Finset.sum_mul]
  ring

end Engine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

section Differences

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def radicalDifferences (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) : Submodule ℂ (LocalGL3 v → ℂ) :=
  Submodule.span ℂ {d : LocalGL3 v → ℂ | ∃ (n : LocalGL3 v) (f' : LocalGL3 v → ℂ),
    f' ∈ principalSeries3 v ![θ, θ, θ'] ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = 1 ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 = 1 ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = 1 ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 = 0 ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧
    d = gl3AmbientRightTranslate (R := ℂ) n f' - f'}

private theorem sub_mem_radicalDifferences (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v ![θ, θ, θ']) (b a : v.adicCompletion ℚ) :
    gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 0 b a) f - f ∈ radicalDifferences v θ θ' := by
  refine Submodule.subset_span ⟨upperUnipotent3 0 b a, f, hf, ?_⟩
  simp [upperUnipotent3_coe]

private theorem rightTranslate_center_mem_radicalDifferences (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (c : (v.adicCompletion ℚ)ˣ) {d : LocalGL3 v → ℂ} (hd : d ∈ radicalDifferences v θ θ') :
    gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) d ∈ radicalDifferences v θ θ' := by
  suffices h : radicalDifferences v θ θ' ≤
      (radicalDifferences v θ θ').comap (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c])) from h hd
  refine Submodule.span_le.mpr ?_
  rintro d ⟨n, f', hf', h00, h11, h22, h01, h10, h20, h21, rfl⟩

  have hn : n = upperUnipotent3 0 ((n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2)
      ((n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h22, h01, h10, h20, h21]
  set b := (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2
  set a := (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2

  have hcomm : upperUnipotent3 0 ((c : v.adicCompletion ℚ)⁻¹ * b) ((c : v.adicCompletion ℚ)⁻¹ * a) *
      diagonal3 v ![1, 1, c] = diagonal3 v ![1, 1, c] * n := by
    rw [radical_mul_center, mul_inv_cancel_left₀ c.ne_zero, mul_inv_cancel_left₀ c.ne_zero, ← hn]
  have hmem := sub_mem_radicalDifferences v θ θ'
    (rightTranslate_mem_principalSeries3 hf' (diagonal3 v ![1, 1, c])) ((c : v.adicCompletion ℚ)⁻¹ * b)
    ((c : v.adicCompletion ℚ)⁻¹ * a)
  rw [SetLike.mem_coe, Submodule.mem_comap, map_sub]
  convert hmem using 2
  all_goals try rfl
  funext g
  simp only [gl3AmbientRightTranslate_apply, mul_assoc, hcomm]

end Differences
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

section Support

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_le_exp_pred_of_lt {x : v.adicCompletion ℚ} {n : ℤ} (h : Valued.v x < WithZero.exp n) :
    Valued.v x ≤ WithZero.exp (n - 1) := by
  by_cases hx : Valued.v x = 0
  · rw [hx]
    exact zero_le'
  · rw [← WithZero.exp_log hx] at h ⊢
    exact WithZero.exp_le_exp.mpr (by have := WithZero.exp_lt_exp.mp h; omega)

private theorem radical_mem_levelBall_of_ne_zero {u : LocalGL3 v → ℂ} (hvan : ∀ g, lowerMinor v g = 0 → u g = 0)
    (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u)
    {g : LocalGL3 v} (hL : lowerMinor v g ≠ 0) (hug : u g ≠ 0) :
    radicalX v g ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) ((n : ℤ) - 1) ∧
      radicalY v g ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) ((n : ℤ) - 1) := by
  have h0 : Valued.v (0 : v.adicCompletion ℚ) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [Valuation.map_zero]
    exact zero_le'
  constructor
  · refine LevelLattice.mem_levelBall.mpr (valued_le_exp_pred_of_lt v (not_le.mp fun hbig => hug ?_))
    have hx0 : radicalX v g ≠ 0 := fun h => by
      rw [h, Valuation.map_zero] at hbig
      exact (not_lt.mpr hbig) WithZero.exp_pos
    have hk := congrFun (hlev _ (level_oppositeRadical v n (valued_neg_inv_le v n hbig) h0)) g
    rw [gl3AmbientRightTranslate_apply] at hk
    rw [← hk]
    exact hvan _ (lowerMinor_mul_oppositeRadical_inv_left v g hL hx0)
  · refine LevelLattice.mem_levelBall.mpr (valued_le_exp_pred_of_lt v (not_le.mp fun hbig => hug ?_))
    have hy0 : radicalY v g ≠ 0 := fun h => by
      rw [h, Valuation.map_zero] at hbig
      exact (not_lt.mpr hbig) WithZero.exp_pos
    have hk := congrFun (hlev _ (level_oppositeRadical v n h0 (valued_neg_inv_le v n hbig))) g
    rw [gl3AmbientRightTranslate_apply] at hk
    rw [← hk]
    exact hvan _ (lowerMinor_mul_oppositeRadical_inv_right v g hL hy0)

end Support
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

section OpenStep

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem mem_cutFirst_iff (n : ℕ) (p q : v.adicCompletion ℚ) (g : LocalGL3 v) :
    g ∈ cutFirst v n p q ↔ lowerMinor v g ≠ 0 ∧ Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1) ∧
      Valued.v (radicalX v g - p) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (radicalY v g - q) ≤ WithZero.exp (-(n : ℤ)) :=
  Iff.rfl

private theorem mem_cutZeroth_iff (n : ℕ) (p q : v.adicCompletion ℚ) (g : LocalGL3 v) :
    g ∈ cutZeroth v n p q ↔ lowerMinor v g ≠ 0 ∧ ¬(Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)) ∧
      Valued.v (radicalX v g - p) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (radicalY v g - q) ≤ WithZero.exp (-(n : ℤ)) :=
  Iff.rfl

private theorem indicator_cut_center_eq_sum (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) {u : LocalGL3 v → ℂ}
    (hu : u ∈ principalSeries3 v ![θ, θ, θ']) (hvan : ∀ g, lowerMinor v g = 0 → u g = 0) (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u)
    (c : (v.adicCompletion ℚ)ˣ) (hc : Valued.v (c : v.adicCompletion ℚ) ≤ 1) (T : Finset (v.adicCompletion ℚ))
    (hTsub : ∀ r ∈ T, r ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))))
    (hT : ∀ a ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))),
      ∃ r ∈ T, a - r ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (hT' : ∀ r ∈ T, ∀ r' ∈ T, r - r' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) → r = r')
    (p q : v.adicCompletion ℚ) (g : LocalGL3 v) :
    ((cutFirst v n p q).indicator u (g * diagonal3 v ![1, 1, c]) =
      (torusChar3 v ![θ, θ, θ'] ![c, 1, 1] * halfModulus3 v ![c, 1, 1]) *
        ∑ r ∈ T, ∑ s ∈ T, (cutFirst v n p q).indicator u
          (g * upperUnipotent3 0 (q - (c : v.adicCompletion ℚ)⁻¹ * q - s)
            (p - (c : v.adicCompletion ℚ)⁻¹ * p - r))) ∧
    ((cutZeroth v n p q).indicator u (g * diagonal3 v ![1, 1, c]) =
      (torusChar3 v ![θ, θ, θ'] ![c, 1, 1] * halfModulus3 v ![c, 1, 1]) *
        ∑ r ∈ T, ∑ s ∈ T, (cutZeroth v n p q).indicator u
          (g * upperUnipotent3 0 (q - (c : v.adicCompletion ℚ)⁻¹ * q - s)
            (p - (c : v.adicCompletion ℚ)⁻¹ * p - r))) := by

  have hzero : ∀ (S : Set (LocalGL3 v)) (h : LocalGL3 v), lowerMinor v h = 0 → S.indicator u h = 0 :=
    fun S h hh => Set.indicator_apply_eq_zero.mpr fun _ => hvan h hh
  by_cases hL : lowerMinor v g = 0
  · have hz : lowerMinor v (g * diagonal3 v ![1, 1, c]) = 0 := by rw [lowerMinor_mul_center]; exact hL
    have hn : ∀ β α : v.adicCompletion ℚ, lowerMinor v (g * upperUnipotent3 0 β α) = 0 := fun β α => by
      rw [lowerMinor_mul_upperUnipotent3]; exact hL
    have hsum0 : ∀ S : Set (LocalGL3 v), ∑ r ∈ T, ∑ s ∈ T, S.indicator u
        (g * upperUnipotent3 0 (q - (c : v.adicCompletion ℚ)⁻¹ * q - s) (p - (c : v.adicCompletion ℚ)⁻¹ * p - r)) =
          0 :=
      fun S => Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => hzero S _ (hn _ _)
    rw [hzero _ _ hz, hzero _ _ hz, hsum0, hsum0, mul_zero]
    exact ⟨rfl, rfl⟩

  have hmiss : ∀ (S : Set (LocalGL3 v)) (D : Prop),
      (∀ h : LocalGL3 v, gl3Entry v h 2 0 = gl3Entry v g 2 0 → gl3Entry v h 2 1 = gl3Entry v g 2 1 →
        h ∈ S → D) → ¬D →
      S.indicator u (g * diagonal3 v ![1, 1, c]) =
        (torusChar3 v ![θ, θ, θ'] ![c, 1, 1] * halfModulus3 v ![c, 1, 1]) *
          ∑ r ∈ T, ∑ s ∈ T, S.indicator u
            (g * upperUnipotent3 0 (q - (c : v.adicCompletion ℚ)⁻¹ * q - s)
              (p - (c : v.adicCompletion ℚ)⁻¹ * p - r)) := by
    intro S D hSD hD
    have hz : g * diagonal3 v ![1, 1, c] ∉ S := fun hmem =>
      hD (hSD _ (gl3Entry_mul_center v g c 2).1 (gl3Entry_mul_center v g c 2).2.1 hmem)
    have hn : ∀ β α : v.adicCompletion ℚ, g * upperUnipotent3 0 β α ∉ S := fun β α hmem =>
      hD (hSD _ (gl3Entry_mul_upperUnipotent3 v g 0 β α 2).1
        (by rw [(gl3Entry_mul_upperUnipotent3 v g 0 β α 2).2.1, mul_zero, add_zero]) hmem)
    have hsum0 : ∑ r ∈ T, ∑ s ∈ T, S.indicator u
        (g * upperUnipotent3 0 (q - (c : v.adicCompletion ℚ)⁻¹ * q - s) (p - (c : v.adicCompletion ℚ)⁻¹ * p - r)) =
          0 :=
      Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => Set.indicator_of_notMem (hn _ _) _
    rw [Set.indicator_of_notMem hz, hsum0, mul_zero]
  by_cases hdisc : Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)
  ·
    have h21 : gl3Entry v g 2 1 ≠ 0 := by
      intro h21
      have h20 : gl3Entry v g 2 0 = 0 := by
        rw [h21, Valuation.map_zero] at hdisc
        exact (Valuation.zero_iff _).mp (le_antisymm hdisc zero_le')
      apply hL
      rw [lowerMinor, h20, h21]
      ring
    obtain ⟨a₀, b₀, e₀, d, hg⟩ := eq_mul_baseOfFirst v g hL h21
    constructor
    · exact indicator_center_eq_sum_of_chart v θ θ' hu n hlev c hc T hTsub hT hT' (cutFirst v n p q)
        (fun a b => Valued.v a ≤ Valued.v b) p q (mem_cutFirst_iff v n p q) g hL hdisc a₀ b₀ e₀ d _ _ _ hg
        (baseOfFirst_mul_center v _ c)
        (fun ξ η => ⟨(section_baseOfFirst v _ ξ η).2.2.2.1, (section_baseOfFirst v _ ξ η).2.2.2.2⟩)
    · exact hmiss (cutZeroth v n p q) (¬(Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)))
        (fun h h0 h1 hmem => by rw [← h0, ← h1]; exact ((mem_cutZeroth_iff v n p q h).mp hmem).2.1)
        (not_not.mpr hdisc)
  ·
    have h20 : gl3Entry v g 2 0 ≠ 0 := by
      intro h20
      apply hdisc
      rw [h20, Valuation.map_zero]
      exact zero_le'
    obtain ⟨a₀, b₀, e₀, d, hg⟩ := eq_mul_baseOfZeroth v g hL h20
    constructor
    · exact hmiss (cutFirst v n p q) (Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1))
        (fun h h0 h1 hmem => by rw [← h0, ← h1]; exact ((mem_cutFirst_iff v n p q h).mp hmem).2.1) hdisc
    · exact indicator_center_eq_sum_of_chart v θ θ' hu n hlev c hc T hTsub hT hT' (cutZeroth v n p q)
        (fun a b => ¬(Valued.v a ≤ Valued.v b)) p q (mem_cutZeroth_iff v n p q) g hL hdisc a₀ b₀ e₀ d _ _ _ hg
        (baseOfZeroth_mul_center v _ c)
        (fun ξ η => ⟨(section_baseOfZeroth v _ ξ η).2.2.2.1, (section_baseOfZeroth v _ ξ η).2.2.2.2⟩)

private theorem eq_sum_indicator_cut {u : LocalGL3 v → ℂ} (hvan : ∀ g, lowerMinor v g = 0 → u g = 0) (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u)
    (T' : Finset (v.adicCompletion ℚ))
    (hT : ∀ a ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) ((n : ℤ) - 1),
      ∃ p ∈ T', a - p ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (hT' : ∀ p ∈ T', ∀ p' ∈ T', p - p' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) → p = p')
    (g : LocalGL3 v) :
    u g = ∑ p ∈ T', ∑ q ∈ T', ((cutFirst v n p q).indicator u g + (cutZeroth v n p q).indicator u g) := by
  classical

  by_cases hL : lowerMinor v g = 0
  · rw [hvan g hL]
    symm
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    rw [(indicator_cut_vanish v hvan n p q g hL).1, (indicator_cut_vanish v hvan n p q g hL).2, add_zero]

  by_cases hug : u g = 0
  · rw [hug]
    symm
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    rw [Set.indicator_apply_eq_zero.mpr fun _ => hug, Set.indicator_apply_eq_zero.mpr fun _ => hug, add_zero]

  obtain ⟨hx, hy⟩ := radical_mem_levelBall_of_ne_zero v hvan n hlev hL hug
  obtain ⟨p, hp, hxp⟩ := hT _ hx
  obtain ⟨q, hq, hyq⟩ := hT _ hy
  have hval : ∀ p' q' : v.adicCompletion ℚ,
      (cutFirst v n p' q').indicator u g + (cutZeroth v n p' q').indicator u g =
        if radicalX v g - p' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) ∧
          radicalY v g - q' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) then u g else 0 := by
    intro p' q'
    by_cases hc : radicalX v g - p' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) ∧
        radicalY v g - q' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ))
    · rw [if_pos hc]
      by_cases hdisc : Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)
      · rw [Set.indicator_of_mem ((mem_cutFirst_iff v n p' q' g).mpr ⟨hL, hdisc, hc.1, hc.2⟩),
          Set.indicator_of_notMem (fun h => ((mem_cutZeroth_iff v n p' q' g).mp h).2.1 hdisc), add_zero]
      · rw [Set.indicator_of_notMem (fun h => hdisc ((mem_cutFirst_iff v n p' q' g).mp h).2.1),
          Set.indicator_of_mem ((mem_cutZeroth_iff v n p' q' g).mpr ⟨hL, hdisc, hc.1, hc.2⟩), zero_add]
    · rw [if_neg hc,
        Set.indicator_of_notMem (fun h => hc ⟨((mem_cutFirst_iff v n p' q' g).mp h).2.2.1,
          ((mem_cutFirst_iff v n p' q' g).mp h).2.2.2⟩),
        Set.indicator_of_notMem (fun h => hc ⟨((mem_cutZeroth_iff v n p' q' g).mp h).2.2.1,
          ((mem_cutZeroth_iff v n p' q' g).mp h).2.2.2⟩), add_zero]
  simp only [hval]
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q, if_pos ⟨hxp, hyq⟩]
  · intro q' hq' hne
    refine if_neg fun hh => hne (hT' q' hq' q hq ?_)
    rw [show q' - q = (radicalY v g - q) - (radicalY v g - q') by abel]
    exact AddSubgroup.sub_mem _ hyq hh.2
  · intro hq'
    exact (hq' hq).elim
  · intro p' hp' hne
    refine Finset.sum_eq_zero fun q' _ => if_neg fun hh => hne (hT' p' hp' p hp ?_)
    rw [show p' - p = (radicalX v g - p) - (radicalX v g - p') by abel]
    exact AddSubgroup.sub_mem _ hxp hh.1
  · intro hp'
    exact (hp' hp).elim

private theorem rightTranslate_center_sub_smul_mem_of_vanishing (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    {u : LocalGL3 v → ℂ} (hu : u ∈ principalSeries3 v ![θ, θ, θ']) (hvan : ∀ g, lowerMinor v g = 0 → u g = 0)
    (n : ℕ) (hn : 1 ≤ n)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u)
    (c : (v.adicCompletion ℚ)ˣ) (hc : Valued.v (c : v.adicCompletion ℚ) ≤ 1) :
    gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) u -
        (((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) • u ∈
      radicalDifferences v θ θ' := by

  have hc0 : (c : v.adicCompletion ℚ) ≠ 0 := c.ne_zero
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (c : v.adicCompletion ℚ) = WithZero.exp k :=
    ⟨WithZero.log (Valued.v (c : v.adicCompletion ℚ)),
      (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hc0)).symm⟩
  have hk0 : k ≤ 0 := by
    rw [hk, ← WithZero.exp_zero] at hc
    exact WithZero.exp_le_exp.mp hc
  obtain ⟨hfin, hcard⟩ := LevelLattice.finite_and_natCard_dilate_levelBall v (-(n : ℤ)) k hk0 _ hk
  haveI := hfin
  obtain ⟨T, hTsub, hT, hT', hTcard⟩ := LevelLattice.exists_finset_transversal
    (LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))))
  obtain ⟨c', hc'⟩ := exists_valued_eq_exp v (1 - 2 * (n : ℤ))
  have hbig : LevelLattice.dilate c' (LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ))) =
      LevelLattice.levelBall ((n : ℤ) - 1) := by
    rw [LevelLattice.dilate_levelBall_eq hc']
    congr 1
    ring
  obtain ⟨hfin', -⟩ := LevelLattice.finite_and_natCard_dilate_levelBall v (-(n : ℤ)) (1 - 2 * (n : ℤ)) (by omega)
    c' hc'
  rw [hbig] at hfin'
  haveI := hfin'
  obtain ⟨T', -, hU, hU', -⟩ := LevelLattice.exists_finset_transversal
    (LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (LevelLattice.levelBall (F := v.adicCompletion ℚ) ((n : ℤ) - 1))

  have hcount : ((T.card : ℝ) : ℂ) = (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ) := by
    rw [hTcard, hcard]
  have hnorm : ((‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc0)
  have hμ : (torusChar3 v ![θ, θ, θ'] ![c, 1, 1] * halfModulus3 v ![c, 1, 1]) * ((T.card : ℂ) * (T.card : ℂ)) =
      ((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ) := by
    rw [law_factor_open, show ((T.card : ℂ)) = ((T.card : ℝ) : ℂ) by norm_cast, hcount, Complex.ofReal_inv,
      mul_assoc, ← mul_assoc ((‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ), mul_inv_cancel₀ hnorm, one_mul]

  set μ : ℂ := ((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)

  have hident : gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) u - μ • u =
      ∑ p ∈ T', ∑ q ∈ T', (torusChar3 v ![θ, θ, θ'] ![c, 1, 1] * halfModulus3 v ![c, 1, 1]) • ∑ r ∈ T, ∑ s ∈ T,
        ((gl3AmbientRightTranslate (R := ℂ)
              (upperUnipotent3 0 (q - (c : v.adicCompletion ℚ)⁻¹ * q - s) (p - (c : v.adicCompletion ℚ)⁻¹ * p - r))
              ((cutFirst v n p q).indicator u) -
            (cutFirst v n p q).indicator u) +
          (gl3AmbientRightTranslate (R := ℂ)
              (upperUnipotent3 0 (q - (c : v.adicCompletion ℚ)⁻¹ * q - s) (p - (c : v.adicCompletion ℚ)⁻¹ * p - r))
              ((cutZeroth v n p q).indicator u) -
            (cutZeroth v n p q).indicator u)) := by
    funext g
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul,
      gl3AmbientRightTranslate_apply]
    rw [eq_sum_indicator_cut v hvan n hlev T' hU hU' (g * diagonal3 v ![1, 1, c]),
      eq_sum_indicator_cut v hvan n hlev T' hU hU' g, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨h1, h0⟩ := indicator_cut_center_eq_sum v θ θ' hu hvan n hlev c hc T hTsub hT hT' p q g
    rw [h1, h0]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [← hμ]
    ring

  rw [hident]
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ ?_
  refine Submodule.sum_mem _ fun r _ => Submodule.sum_mem _ fun s _ => Submodule.add_mem _ ?_ ?_
  · exact sub_mem_radicalDifferences v θ θ' (indicator_cut_mem v hu hvan n p q).1 _ _
  · exact sub_mem_radicalDifferences v θ θ' (indicator_cut_mem v hu hvan n p q).2 _ _

end OpenStep
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem midIndicator_eq_sum_of_reads (v : HeightOneSpectrum (𝓞 ℚ)) (u : LocalGL3 v → ℂ) (S : Set (LocalGL3 v))
    (n : ℕ) (c : (v.adicCompletion ℚ)ˣ) (hc : Valued.v (c : v.adicCompletion ℚ) ≤ 1) (T : Finset (v.adicCompletion ℚ))
    (hTsub : ∀ t ∈ T, t ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))))
    (hT : ∀ a ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))),
      ∃ t ∈ T, a - t ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (hT' : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) → t = t')
    (p ρ : v.adicCompletion ℚ) (φ : v.adicCompletion ℚ → ℂ)
    (hφ : ∀ ρ₁ ρ₂ : v.adicCompletion ℚ, ρ₁ - ρ₂ ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) →
      φ ρ₁ = φ ρ₂)
    (ld lc : ℂ) (gz : LocalGL3 v) (gn : v.adicCompletion ℚ → LocalGL3 v)
    (hz_val : u gz = ld * (lc * φ ((c : v.adicCompletion ℚ) * ρ)))
    (hz_mem : gz ∈ S ↔ (c : v.adicCompletion ℚ) * ρ - p ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (hn_val : ∀ δ : v.adicCompletion ℚ, u (gn δ) = ld * φ (ρ + δ))
    (hn_mem : ∀ δ : v.adicCompletion ℚ,
      gn δ ∈ S ↔ ρ + δ - p ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ))) :
    S.indicator u gz = lc * ∑ t ∈ T, S.indicator u (gn (p - (c : v.adicCompletion ℚ)⁻¹ * p - t)) := by
  set L : AddSubgroup (v.adicCompletion ℚ) := LevelLattice.levelBall (-(n : ℤ))
  have hc0 : (c : v.adicCompletion ℚ) ≠ 0 := c.ne_zero

  have hleft : S.indicator u gz =
      LevelLattice.cosetIndicator L p ((c : v.adicCompletion ℚ) * ρ) *
        (ld * (lc * φ ((c : v.adicCompletion ℚ) * ρ))) := by
    by_cases h : (c : v.adicCompletion ℚ) * ρ - p ∈ L
    · rw [Set.indicator_of_mem (hz_mem.2 h), LevelLattice.cosetIndicator_of_mem h, one_mul, hz_val]
    · rw [Set.indicator_of_notMem (fun hm => h (hz_mem.1 hm)), LevelLattice.cosetIndicator_of_not h, zero_mul]

  have hterm : ∀ t ∈ T, S.indicator u (gn (p - (c : v.adicCompletion ℚ)⁻¹ * p - t)) =
      LevelLattice.cosetIndicator L ((c : v.adicCompletion ℚ)⁻¹ * p + t) ρ *
        (ld * φ ((c : v.adicCompletion ℚ) * ρ)) := by
    intro t ht
    have hshape : ρ + (p - (c : v.adicCompletion ℚ)⁻¹ * p - t) - p = ρ - ((c : v.adicCompletion ℚ)⁻¹ * p + t) := by
      ring
    by_cases hcond : ρ - ((c : v.adicCompletion ℚ)⁻¹ * p + t) ∈ L
    · have hmem : gn (p - (c : v.adicCompletion ℚ)⁻¹ * p - t) ∈ S := by
        rw [hn_mem, hshape]
        exact hcond
      rw [Set.indicator_of_mem hmem, LevelLattice.cosetIndicator_of_mem hcond, one_mul, hn_val]
      congr 1
      apply hφ
      have e : ρ + (p - (c : v.adicCompletion ℚ)⁻¹ * p - t) - (c : v.adicCompletion ℚ) * ρ =
          (ρ - ((c : v.adicCompletion ℚ)⁻¹ * p + t)) -
            ((c : v.adicCompletion ℚ) * (ρ - ((c : v.adicCompletion ℚ)⁻¹ * p + t)) +
              (c : v.adicCompletion ℚ) * t) := by
        rw [mul_sub, mul_add, mul_inv_cancel_left₀ hc0]
        ring
      rw [e]
      exact L.sub_mem hcond (L.add_mem (LevelLattice.mem_dilate.mp (LevelLattice.levelBall_le_dilate hc hcond))
        (LevelLattice.mem_dilate.mp (hTsub t ht)))
    · have hnot : gn (p - (c : v.adicCompletion ℚ)⁻¹ * p - t) ∉ S := by
        rw [hn_mem, hshape]
        exact hcond
      rw [Set.indicator_of_notMem hnot, LevelLattice.cosetIndicator_of_not hcond, zero_mul]

  have hsum : LevelLattice.cosetIndicator L p ((c : v.adicCompletion ℚ) * ρ) =
      ∑ t ∈ T, LevelLattice.cosetIndicator L ((c : v.adicCompletion ℚ)⁻¹ * p + t) ρ :=
    congrFun (LevelLattice.cosetIndicator_mul L (c : v.adicCompletion ℚ) hc0 (LevelLattice.levelBall_le_dilate hc) T
      hTsub hT hT' p) ρ
  rw [hleft, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← hsum]
  ring

private theorem indicator_midCutFirst_center_eq_sum (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {u : LocalGL3 v → ℂ} (hu : u ∈ principalSeries3 v χ) (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u)
    (c : (v.adicCompletion ℚ)ˣ) (hc : Valued.v (c : v.adicCompletion ℚ) ≤ 1) (T : Finset (v.adicCompletion ℚ))
    (hTsub : ∀ t ∈ T, t ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))))
    (hT : ∀ a ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))),
      ∃ t ∈ T, a - t ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (hT' : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) → t = t')
    (p : v.adicCompletion ℚ) (g : LocalGL3 v) (hL : lowerMinor v g = 0) (h21 : gl3Entry v g 2 1 ≠ 0)
    (hD : Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)) :
    (midCutFirst v n p).indicator u (g * diagonal3 v ![1, 1, c]) =
      (torusChar3 v χ ![1, c, 1] * halfModulus3 v ![1, c, 1]) *
        ∑ t ∈ T, (midCutFirst v n p).indicator u
          (g * upperUnipotent3 0 (p - (c : v.adicCompletion ℚ)⁻¹ * p - t) 0) := by
  obtain ⟨a, b, e, d, hg⟩ := eq_mul_midBaseOfFirst v g hL h21
  set s := gl3Entry v g 2 0 / gl3Entry v g 2 1
  set ρ := gl3Entry v g 2 2 / gl3Entry v g 2 1 with hρ
  refine midIndicator_eq_sum_of_reads v u (midCutFirst v n p) n c hc T hTsub hT hT' p ρ
    (fun ρ' => u (midBaseOfFirst v s * upperUnipotent3 0 ρ' 0)) ?_ (torusChar3 v χ d * halfModulus3 v d)
    (torusChar3 v χ ![1, c, 1] * halfModulus3 v ![1, c, 1]) (g * diagonal3 v ![1, 1, c])
    (fun δ => g * upperUnipotent3 0 δ 0) ?_ ?_ ?_ ?_
  ·
    intro ρ₁ ρ₂ h
    have hk := congrFun (hlev (upperUnipotent3 0 (ρ₁ - ρ₂) 0)
      (level_radical v n (by simp) (LevelLattice.mem_levelBall.mp h))) (midBaseOfFirst v s * upperUnipotent3 0 ρ₂ 0)
    rw [gl3AmbientRightTranslate_apply, mul_assoc, radical_mul, add_zero, add_sub_cancel] at hk
    exact hk
  ·
    have hz : g * diagonal3 v ![1, 1, c] = upperUnipotent3 a b e * (diagonal3 v d * (diagonal3 v ![1, c, 1] *
        (midBaseOfFirst v s * upperUnipotent3 0 ((c : v.adicCompletion ℚ) * ρ) 0))) := by
      rw [hg]
      simp only [mul_assoc]
      rw [radical_mul_center, mul_zero, ← mul_assoc (midBaseOfFirst v s), midBaseOfFirst_mul_center, mul_assoc]
    show u (g * diagonal3 v ![1, 1, c]) =
      _ * (_ * u (midBaseOfFirst v s * upperUnipotent3 0 ((c : v.adicCompletion ℚ) * ρ) 0))
    rw [hz, apply_upperUnipotent3_mul_of_mem_principalSeries3 hu, apply_diagonal3_mul_of_mem_principalSeries3 hu,
      apply_diagonal3_mul_of_mem_principalSeries3 hu]
  ·
    obtain ⟨h0, h1, h2⟩ := gl3Entry_mul_center v g c 2
    simp only [midCutFirst, Set.mem_setOf_eq, h0, h1, h2, LevelLattice.mem_levelBall]
    rw [show gl3Entry v g 2 2 * (c : v.adicCompletion ℚ) / gl3Entry v g 2 1 = (c : v.adicCompletion ℚ) * ρ by
      rw [hρ]; ring]
    exact and_iff_right hD
  ·
    intro δ
    have hn : g * upperUnipotent3 0 δ 0 =
        upperUnipotent3 a b e * (diagonal3 v d * (midBaseOfFirst v s * upperUnipotent3 0 (ρ + δ) 0)) := by
      rw [hg]
      simp only [mul_assoc]
      rw [radical_mul, add_zero]
    show u (g * upperUnipotent3 0 δ 0) = _ * u (midBaseOfFirst v s * upperUnipotent3 0 (ρ + δ) 0)
    rw [hn, apply_upperUnipotent3_mul_of_mem_principalSeries3 hu, apply_diagonal3_mul_of_mem_principalSeries3 hu]
  ·
    intro δ
    obtain ⟨h0, h1, h2⟩ := gl3Entry_mul_upperUnipotent3 v g 0 δ 0 2
    rw [mul_zero, add_zero] at h1
    rw [mul_zero, add_zero] at h2
    show g * upperUnipotent3 0 δ 0 ∈ midCutFirst v n p ↔ _
    simp only [midCutFirst, Set.mem_setOf_eq, h0, h1, h2, LevelLattice.mem_levelBall]
    rw [show (gl3Entry v g 2 2 + gl3Entry v g 2 1 * δ) / gl3Entry v g 2 1 = ρ + δ by rw [hρ]; field_simp]
    exact and_iff_right hD

private theorem indicator_midCutZeroth_center_eq_sum (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {u : LocalGL3 v → ℂ} (hu : u ∈ principalSeries3 v χ) (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u)
    (c : (v.adicCompletion ℚ)ˣ) (hc : Valued.v (c : v.adicCompletion ℚ) ≤ 1) (T : Finset (v.adicCompletion ℚ))
    (hTsub : ∀ t ∈ T, t ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))))
    (hT : ∀ a ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))),
      ∃ t ∈ T, a - t ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (hT' : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) → t = t')
    (p : v.adicCompletion ℚ) (g : LocalGL3 v) (hL : lowerMinor v g = 0) (h20 : gl3Entry v g 2 0 ≠ 0)
    (hD : ¬(Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1))) :
    (midCutZeroth v n p).indicator u (g * diagonal3 v ![1, 1, c]) =
      (torusChar3 v χ ![1, c, 1] * halfModulus3 v ![1, c, 1]) *
        ∑ t ∈ T, (midCutZeroth v n p).indicator u
          (g * upperUnipotent3 0 0 (p - (c : v.adicCompletion ℚ)⁻¹ * p - t)) := by
  obtain ⟨a, b, e, d, hg⟩ := eq_mul_midBaseOfZeroth v g hL h20
  set s := gl3Entry v g 2 1 / gl3Entry v g 2 0
  set ρ := gl3Entry v g 2 2 / gl3Entry v g 2 0 with hρ
  refine midIndicator_eq_sum_of_reads v u (midCutZeroth v n p) n c hc T hTsub hT hT' p ρ
    (fun ρ' => u (midBaseOfZeroth v s * upperUnipotent3 0 0 ρ')) ?_ (torusChar3 v χ d * halfModulus3 v d)
    (torusChar3 v χ ![1, c, 1] * halfModulus3 v ![1, c, 1]) (g * diagonal3 v ![1, 1, c])
    (fun δ => g * upperUnipotent3 0 0 δ) ?_ ?_ ?_ ?_
  · intro ρ₁ ρ₂ h
    have hk := congrFun (hlev (upperUnipotent3 0 0 (ρ₁ - ρ₂))
      (level_radical v n (LevelLattice.mem_levelBall.mp h) (by simp))) (midBaseOfZeroth v s * upperUnipotent3 0 0 ρ₂)
    rw [gl3AmbientRightTranslate_apply, mul_assoc, radical_mul, add_zero, add_sub_cancel] at hk
    exact hk
  · have hz : g * diagonal3 v ![1, 1, c] = upperUnipotent3 a b e * (diagonal3 v d * (diagonal3 v ![1, c, 1] *
        (midBaseOfZeroth v s * upperUnipotent3 0 0 ((c : v.adicCompletion ℚ) * ρ)))) := by
      rw [hg]
      simp only [mul_assoc]
      rw [radical_mul_center, mul_zero, ← mul_assoc (midBaseOfZeroth v s), midBaseOfZeroth_mul_center, mul_assoc]
    show u (g * diagonal3 v ![1, 1, c]) =
      _ * (_ * u (midBaseOfZeroth v s * upperUnipotent3 0 0 ((c : v.adicCompletion ℚ) * ρ)))
    rw [hz, apply_upperUnipotent3_mul_of_mem_principalSeries3 hu, apply_diagonal3_mul_of_mem_principalSeries3 hu,
      apply_diagonal3_mul_of_mem_principalSeries3 hu]
  · obtain ⟨h0, h1, h2⟩ := gl3Entry_mul_center v g c 2
    simp only [midCutZeroth, Set.mem_setOf_eq, h0, h1, h2, LevelLattice.mem_levelBall]
    rw [show gl3Entry v g 2 2 * (c : v.adicCompletion ℚ) / gl3Entry v g 2 0 = (c : v.adicCompletion ℚ) * ρ by
      rw [hρ]; ring]
    exact and_iff_right hD
  · intro δ
    have hn : g * upperUnipotent3 0 0 δ =
        upperUnipotent3 a b e * (diagonal3 v d * (midBaseOfZeroth v s * upperUnipotent3 0 0 (ρ + δ))) := by
      rw [hg]
      simp only [mul_assoc]
      rw [radical_mul, add_zero]
    show u (g * upperUnipotent3 0 0 δ) = _ * u (midBaseOfZeroth v s * upperUnipotent3 0 0 (ρ + δ))
    rw [hn, apply_upperUnipotent3_mul_of_mem_principalSeries3 hu, apply_diagonal3_mul_of_mem_principalSeries3 hu]
  · intro δ
    obtain ⟨h0, h1, h2⟩ := gl3Entry_mul_upperUnipotent3 v g 0 0 δ 2
    rw [mul_zero, add_zero] at h1
    rw [mul_zero, add_zero] at h2
    show g * upperUnipotent3 0 0 δ ∈ midCutZeroth v n p ↔ _
    simp only [midCutZeroth, Set.mem_setOf_eq, h0, h1, h2, LevelLattice.mem_levelBall]
    rw [show (gl3Entry v g 2 2 + gl3Entry v g 2 0 * δ) / gl3Entry v g 2 0 = ρ + δ by rw [hρ]; field_simp]
    exact and_iff_right hD

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem mem_midCutFirst_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (p : v.adicCompletion ℚ) (g : LocalGL3 v) :
    g ∈ midCutFirst v n p ↔ Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1) ∧
      Valued.v (gl3Entry v g 2 2 / gl3Entry v g 2 1 - p) ≤ WithZero.exp (-(n : ℤ)) :=
  Iff.rfl

private theorem mem_midCutZeroth_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (p : v.adicCompletion ℚ) (g : LocalGL3 v) :
    g ∈ midCutZeroth v n p ↔ ¬ Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1) ∧
      Valued.v (gl3Entry v g 2 2 / gl3Entry v g 2 0 - p) ≤ WithZero.exp (-(n : ℤ)) :=
  Iff.rfl

private theorem apply_eq_zero_of_first_of_not_le (v : HeightOneSpectrum (𝓞 ℚ)) {u : LocalGL3 v → ℂ}
    (hP : ∀ g : LocalGL3 v, gl3Entry v g 2 0 = 0 → gl3Entry v g 2 1 = 0 → u g = 0) (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u)
    (g : LocalGL3 v) (hD : Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1))
    (hbig : ¬ Valued.v (gl3Entry v g 2 2 / gl3Entry v g 2 1) ≤ WithZero.exp (n : ℤ)) : u g = 0 := by
  have h22 : gl3Entry v g 2 2 ≠ 0 := fun h => hbig (by simp [h])
  have hb : Valued.v (-(gl3Entry v g 2 1 / gl3Entry v g 2 2)) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← inv_div]
    exact valued_neg_inv_le v n (not_le.mp hbig).le
  have ha : Valued.v (-(gl3Entry v g 2 0 / gl3Entry v g 2 2)) ≤ WithZero.exp (-(n : ℤ)) := by
    have hb' := hb
    rw [Valuation.map_neg, div_eq_inv_mul] at hb'
    rw [Valuation.map_neg, div_eq_inv_mul]
    exact ((valued_mul_le_valued_mul_iff v (inv_ne_zero h22) _ _).mpr hD).trans hb'
  obtain ⟨k0, k1⟩ := bottom_mul_oppositeRadical_div v g h22
  have hk := congrFun (hlev _ (level_oppositeRadical v n ha hb)) g
  rw [gl3AmbientRightTranslate_apply, hP _ k0 k1] at hk
  exact hk.symm

private theorem apply_eq_zero_of_zeroth_of_not_le (v : HeightOneSpectrum (𝓞 ℚ)) {u : LocalGL3 v → ℂ}
    (hP : ∀ g : LocalGL3 v, gl3Entry v g 2 0 = 0 → gl3Entry v g 2 1 = 0 → u g = 0) (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u)
    (g : LocalGL3 v) (hD : ¬ Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1))
    (hbig : ¬ Valued.v (gl3Entry v g 2 2 / gl3Entry v g 2 0) ≤ WithZero.exp (n : ℤ)) : u g = 0 := by
  have h22 : gl3Entry v g 2 2 ≠ 0 := fun h => hbig (by simp [h])
  have ha : Valued.v (-(gl3Entry v g 2 0 / gl3Entry v g 2 2)) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← inv_div]
    exact valued_neg_inv_le v n (not_le.mp hbig).le
  have hb : Valued.v (-(gl3Entry v g 2 1 / gl3Entry v g 2 2)) ≤ WithZero.exp (-(n : ℤ)) := by
    have ha' := ha
    rw [Valuation.map_neg, div_eq_inv_mul] at ha'
    rw [Valuation.map_neg, div_eq_inv_mul]
    exact ((valued_mul_le_valued_mul_iff v (inv_ne_zero h22) _ _).mpr (not_le.mp hD).le).trans ha'
  obtain ⟨k0, k1⟩ := bottom_mul_oppositeRadical_div v g h22
  have hk := congrFun (hlev _ (level_oppositeRadical v n ha hb)) g
  rw [gl3AmbientRightTranslate_apply, hP _ k0 k1] at hk
  exact hk.symm

private theorem sum_cosetIndicator_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (T' : Finset (v.adicCompletion ℚ))
    (hcov : ∀ a ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (n : ℤ),
      ∃ p ∈ T', a - p ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (hinc : ∀ p ∈ T', ∀ p' ∈ T', p - p' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) → p = p')
    {r : v.adicCompletion ℚ} (hr : r ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (n : ℤ)) :
    ∑ p ∈ T', LevelLattice.cosetIndicator (LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ))) p r = 1 := by
  set L : AddSubgroup (v.adicCompletion ℚ) := LevelLattice.levelBall (-(n : ℤ))
  obtain ⟨p₀, hp₀, hrp₀⟩ := hcov r hr
  rw [Finset.sum_eq_single p₀]
  · exact LevelLattice.cosetIndicator_of_mem hrp₀
  · intro p hp hne
    refine LevelLattice.cosetIndicator_of_not fun hrp => hne (hinc p hp p₀ hp₀ ?_)
    have e : p - p₀ = (r - p₀) - (r - p) := by ring
    rw [e]
    exact L.sub_mem hrp₀ hrp
  · intro h
    exact absurd hp₀ h

private theorem indicator_midCutFirst_apply (v : HeightOneSpectrum (𝓞 ℚ)) (u : LocalGL3 v → ℂ) (n : ℕ)
    (p : v.adicCompletion ℚ) (g : LocalGL3 v) (hD : Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)) :
    (midCutFirst v n p).indicator u g =
      LevelLattice.cosetIndicator (LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ))) p
        (gl3Entry v g 2 2 / gl3Entry v g 2 1) * u g := by
  by_cases h : gl3Entry v g 2 2 / gl3Entry v g 2 1 - p ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ))
  · rw [LevelLattice.cosetIndicator_of_mem h, one_mul]
    exact Set.indicator_of_mem ((mem_midCutFirst_iff v n p g).mpr ⟨hD, LevelLattice.mem_levelBall.mp h⟩) u
  · rw [LevelLattice.cosetIndicator_of_not h, zero_mul]
    exact Set.indicator_of_notMem
      (fun hm => h (LevelLattice.mem_levelBall.mpr ((mem_midCutFirst_iff v n p g).mp hm).2)) u

private theorem indicator_midCutZeroth_apply (v : HeightOneSpectrum (𝓞 ℚ)) (u : LocalGL3 v → ℂ) (n : ℕ)
    (p : v.adicCompletion ℚ) (g : LocalGL3 v) (hD : ¬ Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)) :
    (midCutZeroth v n p).indicator u g =
      LevelLattice.cosetIndicator (LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ))) p
        (gl3Entry v g 2 2 / gl3Entry v g 2 0) * u g := by
  by_cases h : gl3Entry v g 2 2 / gl3Entry v g 2 0 - p ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ))
  · rw [LevelLattice.cosetIndicator_of_mem h, one_mul]
    exact Set.indicator_of_mem ((mem_midCutZeroth_iff v n p g).mpr ⟨hD, LevelLattice.mem_levelBall.mp h⟩) u
  · rw [LevelLattice.cosetIndicator_of_not h, zero_mul]
    exact Set.indicator_of_notMem
      (fun hm => h (LevelLattice.mem_levelBall.mpr ((mem_midCutZeroth_iff v n p g).mp hm).2)) u

private theorem eq_sum_indicator_midCut_of_lowerMinor_eq_zero (v : HeightOneSpectrum (𝓞 ℚ)) {u : LocalGL3 v → ℂ}
    (hP : ∀ g : LocalGL3 v, gl3Entry v g 2 0 = 0 → gl3Entry v g 2 1 = 0 → u g = 0) (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u)
    (T' : Finset (v.adicCompletion ℚ))
    (hcov : ∀ a ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (n : ℤ),
      ∃ p ∈ T', a - p ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (hinc : ∀ p ∈ T', ∀ p' ∈ T', p - p' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) → p = p')
    (g : LocalGL3 v) :
    u g = ∑ p ∈ T', ((midCutFirst v n p).indicator u g + (midCutZeroth v n p).indicator u g) := by
  by_cases hu0 : u g = 0
  ·
    rw [hu0]
    refine (Finset.sum_eq_zero fun p _ => ?_).symm
    classical
    simp [Set.indicator_apply, hu0]
  by_cases hD : Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)
  ·
    have hr : gl3Entry v g 2 2 / gl3Entry v g 2 1 ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (n : ℤ) := by
      rw [LevelLattice.mem_levelBall]
      by_contra hbig
      exact hu0 (apply_eq_zero_of_first_of_not_le v hP n hlev g hD hbig)
    have hterm : ∀ p ∈ T', (midCutFirst v n p).indicator u g + (midCutZeroth v n p).indicator u g =
        LevelLattice.cosetIndicator (LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ))) p
          (gl3Entry v g 2 2 / gl3Entry v g 2 1) * u g := by
      intro p _
      rw [indicator_midCutFirst_apply v u n p g hD,
        Set.indicator_of_notMem (fun hm => ((mem_midCutZeroth_iff v n p g).mp hm).1 hD) u, add_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_cosetIndicator_eq_one v n T' hcov hinc hr, one_mul]
  ·
    have hr : gl3Entry v g 2 2 / gl3Entry v g 2 0 ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (n : ℤ) := by
      rw [LevelLattice.mem_levelBall]
      by_contra hbig
      exact hu0 (apply_eq_zero_of_zeroth_of_not_le v hP n hlev g hD hbig)
    have hterm : ∀ p ∈ T', (midCutFirst v n p).indicator u g + (midCutZeroth v n p).indicator u g =
        LevelLattice.cosetIndicator (LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ))) p
          (gl3Entry v g 2 2 / gl3Entry v g 2 0) * u g := by
      intro p _
      rw [indicator_midCutZeroth_apply v u n p g hD,
        Set.indicator_of_notMem (fun hm => hD ((mem_midCutFirst_iff v n p g).mp hm).1) u, zero_add]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_cosetIndicator_eq_one v n T' hcov hinc hr, one_mul]

private theorem indicator_midCutFirst_center_eq_sum_of_lowerMinor_eq_zero (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {u : LocalGL3 v → ℂ} (hu : u ∈ principalSeries3 v χ)
    (hP : ∀ g : LocalGL3 v, gl3Entry v g 2 0 = 0 → gl3Entry v g 2 1 = 0 → u g = 0) (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u)
    (c : (v.adicCompletion ℚ)ˣ) (hc : Valued.v (c : v.adicCompletion ℚ) ≤ 1) (T : Finset (v.adicCompletion ℚ))
    (hTsub : ∀ t ∈ T, t ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))))
    (hT : ∀ a ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))),
      ∃ t ∈ T, a - t ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (hT' : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) → t = t')
    (p : v.adicCompletion ℚ) (g : LocalGL3 v) (hL : lowerMinor v g = 0) :
    (midCutFirst v n p).indicator u (g * diagonal3 v ![1, 1, c]) =
      (torusChar3 v χ ![1, c, 1] * halfModulus3 v ![1, c, 1]) *
        ∑ t ∈ T, (midCutFirst v n p).indicator u
          (g * upperUnipotent3 0 (p - (c : v.adicCompletion ℚ)⁻¹ * p - t) 0) := by
  obtain ⟨z0, z1, -⟩ := gl3Entry_mul_center v g c 2
  by_cases hcl : gl3Entry v g 2 0 = 0 ∧ gl3Entry v g 2 1 = 0
  ·
    rw [(indicator_midCut_vanish v hP n p _ (z0.trans hcl.1) (z1.trans hcl.2)).1, Finset.sum_eq_zero, mul_zero]
    intro t _
    obtain ⟨n0, n1, -⟩ := gl3Entry_mul_upperUnipotent3 v g 0 (p - (c : v.adicCompletion ℚ)⁻¹ * p - t) 0 2
    rw [mul_zero, add_zero] at n1
    exact (indicator_midCut_vanish v hP n p _ (n0.trans hcl.1) (n1.trans hcl.2)).1
  by_cases hD : Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)
  ·
    have h21 : gl3Entry v g 2 1 ≠ 0 := fun h21 => hcl ⟨by
      rw [h21, Valuation.map_zero] at hD
      exact (Valuation.zero_iff _).mp (le_antisymm hD zero_le'), h21⟩
    exact indicator_midCutFirst_center_eq_sum v χ hu n hlev c hc T hTsub hT hT' p g hL h21 hD
  ·
    have hz : g * diagonal3 v ![1, 1, c] ∉ midCutFirst v n p := fun hm => by
      have h := ((mem_midCutFirst_iff v n p _).mp hm).1
      rw [z0, z1] at h
      exact hD h
    rw [Set.indicator_of_notMem hz u, Finset.sum_eq_zero, mul_zero]
    intro t _
    obtain ⟨n0, n1, -⟩ := gl3Entry_mul_upperUnipotent3 v g 0 (p - (c : v.adicCompletion ℚ)⁻¹ * p - t) 0 2
    rw [mul_zero, add_zero] at n1
    refine Set.indicator_of_notMem (fun hm => ?_) u
    have h := ((mem_midCutFirst_iff v n p _).mp hm).1
    rw [n0, n1] at h
    exact hD h

private theorem indicator_midCutZeroth_center_eq_sum_of_lowerMinor_eq_zero (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {u : LocalGL3 v → ℂ} (hu : u ∈ principalSeries3 v χ)
    (hP : ∀ g : LocalGL3 v, gl3Entry v g 2 0 = 0 → gl3Entry v g 2 1 = 0 → u g = 0) (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u)
    (c : (v.adicCompletion ℚ)ˣ) (hc : Valued.v (c : v.adicCompletion ℚ) ≤ 1) (T : Finset (v.adicCompletion ℚ))
    (hTsub : ∀ t ∈ T, t ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))))
    (hT : ∀ a ∈ LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))),
      ∃ t ∈ T, a - t ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (hT' : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)) → t = t')
    (p : v.adicCompletion ℚ) (g : LocalGL3 v) (hL : lowerMinor v g = 0) :
    (midCutZeroth v n p).indicator u (g * diagonal3 v ![1, 1, c]) =
      (torusChar3 v χ ![1, c, 1] * halfModulus3 v ![1, c, 1]) *
        ∑ t ∈ T, (midCutZeroth v n p).indicator u
          (g * upperUnipotent3 0 0 (p - (c : v.adicCompletion ℚ)⁻¹ * p - t)) := by
  obtain ⟨z0, z1, -⟩ := gl3Entry_mul_center v g c 2
  by_cases hcl : gl3Entry v g 2 0 = 0 ∧ gl3Entry v g 2 1 = 0
  · rw [(indicator_midCut_vanish v hP n p _ (z0.trans hcl.1) (z1.trans hcl.2)).2, Finset.sum_eq_zero, mul_zero]
    intro t _
    obtain ⟨n0, n1, -⟩ := gl3Entry_mul_upperUnipotent3 v g 0 0 (p - (c : v.adicCompletion ℚ)⁻¹ * p - t) 2
    rw [mul_zero, add_zero] at n1
    exact (indicator_midCut_vanish v hP n p _ (n0.trans hcl.1) (n1.trans hcl.2)).2
  by_cases hD : Valued.v (gl3Entry v g 2 0) ≤ Valued.v (gl3Entry v g 2 1)
  ·
    have hz : g * diagonal3 v ![1, 1, c] ∉ midCutZeroth v n p := fun hm => by
      refine ((mem_midCutZeroth_iff v n p _).mp hm).1 ?_
      rw [z0, z1]
      exact hD
    rw [Set.indicator_of_notMem hz u, Finset.sum_eq_zero, mul_zero]
    intro t _
    obtain ⟨n0, n1, -⟩ := gl3Entry_mul_upperUnipotent3 v g 0 0 (p - (c : v.adicCompletion ℚ)⁻¹ * p - t) 2
    rw [mul_zero, add_zero] at n1
    refine Set.indicator_of_notMem (fun hm => ((mem_midCutZeroth_iff v n p _).mp hm).1 ?_) u
    rw [n0, n1]
    exact hD
  ·
    have h20 : gl3Entry v g 2 0 ≠ 0 := fun h20 => hD (by
      rw [h20, Valuation.map_zero]
      exact zero_le')
    exact indicator_midCutZeroth_center_eq_sum v χ hu n hlev c hc T hTsub hT hT' p g hL h20 hD

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem exists_radicalDifference_middle (v : HeightOneSpectrum (𝓞 ℚ))
    (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v ![θ, θ, θ'])
    (hP : ∀ g : LocalGL3 v, gl3Entry v g 2 0 = 0 → gl3Entry v g 2 1 = 0 → f g = 0) (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k f = f)
    (c : (v.adicCompletion ℚ)ˣ) (hc : Valued.v (c : v.adicCompletion ℚ) ≤ 1) :
    ∃ d ∈ radicalDifferences v θ θ', ∀ g : LocalGL3 v, lowerMinor v g = 0 →
      (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) f -
        (((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) • f - d) g = 0 := by

  have hc0 : (c : v.adicCompletion ℚ) ≠ 0 := c.ne_zero
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (c : v.adicCompletion ℚ) = WithZero.exp k :=
    ⟨WithZero.log (Valued.v (c : v.adicCompletion ℚ)),
      (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hc0)).symm⟩
  have hk0 : k ≤ 0 := by
    rw [hk, ← WithZero.exp_zero] at hc
    exact WithZero.exp_le_exp.mp hc
  obtain ⟨hfin, hcard⟩ := LevelLattice.finite_and_natCard_dilate_levelBall v (-(n : ℤ)) k hk0 _ hk
  haveI := hfin
  obtain ⟨T, hTsub, hT, hT', hTcard⟩ := LevelLattice.exists_finset_transversal
    (LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (LevelLattice.dilate (c : v.adicCompletion ℚ) (LevelLattice.levelBall (-(n : ℤ))))

  obtain ⟨c', hc'⟩ := exists_valued_eq_exp v (-(2 * (n : ℤ)))
  have hbig : LevelLattice.dilate c' (LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ))) =
      LevelLattice.levelBall (n : ℤ) := by
    rw [LevelLattice.dilate_levelBall_eq hc']
    congr 1
    ring
  obtain ⟨hfin', -⟩ := LevelLattice.finite_and_natCard_dilate_levelBall v (-(n : ℤ)) (-(2 * (n : ℤ))) (by omega) c' hc'
  rw [hbig] at hfin'
  haveI := hfin'
  obtain ⟨T', -, hcov, hinc, -⟩ := LevelLattice.exists_finset_transversal
    (LevelLattice.levelBall (F := v.adicCompletion ℚ) (-(n : ℤ)))
    (LevelLattice.levelBall (F := v.adicCompletion ℚ) (n : ℤ))

  have hcount : ((T.card : ℝ) : ℂ) = (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ) := by
    rw [hTcard, hcard]
  have hμ : (torusChar3 v ![θ, θ, θ'] ![1, c, 1] * halfModulus3 v ![1, c, 1]) * (T.card : ℂ) =
      ((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ) := by
    rw [law_factor_middle, show ((T.card : ℂ)) = ((T.card : ℝ) : ℂ) by norm_cast, hcount]

  refine ⟨∑ p ∈ T', ∑ t ∈ T, (torusChar3 v ![θ, θ, θ'] ![1, c, 1] * halfModulus3 v ![1, c, 1]) •
      ((gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 0 (p - (c : v.adicCompletion ℚ)⁻¹ * p - t) 0)
          ((midCutFirst v n p).indicator f) - (midCutFirst v n p).indicator f) +
        (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 0 0 (p - (c : v.adicCompletion ℚ)⁻¹ * p - t))
          ((midCutZeroth v n p).indicator f) - (midCutZeroth v n p).indicator f)), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun t _ =>
      Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
    · exact sub_mem_radicalDifferences v θ θ' (indicator_midCut_mem v hf hP n p).1 _ _
    · exact sub_mem_radicalDifferences v θ θ' (indicator_midCut_mem v hf hP n p).2 _ _

  intro g hL
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.add_apply,
    gl3AmbientRightTranslate_apply]
  rw [eq_sum_indicator_midCut_of_lowerMinor_eq_zero v hP n hlev T' hcov hinc (g * diagonal3 v ![1, 1, c]),
    eq_sum_indicator_midCut_of_lowerMinor_eq_zero v hP n hlev T' hcov hinc g, ← hμ, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [indicator_midCutFirst_center_eq_sum_of_lowerMinor_eq_zero v _ hf hP n hlev c hc T hTsub hT hT' p g hL,
    indicator_midCutZeroth_center_eq_sum_of_lowerMinor_eq_zero v _ hf hP n hlev c hc T hTsub hT hT' p g hL]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.mul_sum]
  ring

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ParabolicCharts
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

section Assembly

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem radicalDifferences_le (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) :
    radicalDifferences v θ θ' ≤ principalSeries3 v ![θ, θ, θ'] := by
  refine Submodule.span_le.mpr ?_
  rintro d ⟨n, f', hf', -, -, -, -, -, -, -, rfl⟩
  exact (principalSeries3 v ![θ, θ, θ']).sub_mem (rightTranslate_mem_principalSeries3 hf' n) hf'

private theorem level_succ {u : LocalGL3 v → ℂ} (n : ℕ)
    (hlev : ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-(n : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u) :
    ∀ k : LocalGL3 v,
      (∀ i j : Fin 3,
        Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
          WithZero.exp (-((n + 1 : ℕ) : ℤ))) →
      gl3AmbientRightTranslate (R := ℂ) k u = u :=
  fun k hk => hlev k fun i j => (hk i j).trans (WithZero.exp_le_exp.mpr (by omega))

private theorem annihilator_sq_mem_of_valued_le_one (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hunif : ∀ f : LocalGL3 v → ℂ, f ∈ principalSeries3 v ![θ, θ, θ'] →
      ∃ n : ℕ, ∀ k : LocalGL3 v,
        (∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
            ≤ WithZero.exp (-(n : ℤ))) →
        gl3AmbientRightTranslate (R := ℂ) k f = f)
    (c : (v.adicCompletion ℚ)ˣ) (hc : Valued.v (c : v.adicCompletion ℚ) ≤ 1) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v ![θ, θ, θ'])
    (hP : ∀ g : LocalGL3 v, gl3Entry v g 2 0 = 0 → gl3Entry v g 2 1 = 0 → f g = 0) :
    ((gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) -
        (((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) • (1 : Module.End ℂ (LocalGL3 v → ℂ))) ^ 2) f ∈
      radicalDifferences v θ θ' := by
  obtain ⟨n₀, hn₀⟩ := hunif f hf
  obtain ⟨d, hd, hw⟩ := exists_radicalDifference_middle v θ θ' hf hP n₀ hn₀ c hc
  set μ : ℂ := ((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)
  set w : LocalGL3 v → ℂ := gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) f - μ • f - d with hw_def
  have hwmem : w ∈ principalSeries3 v ![θ, θ, θ'] :=
    Submodule.sub_mem _ (Submodule.sub_mem _ (rightTranslate_mem_principalSeries3 hf _) (Submodule.smul_mem _ _ hf))
      (radicalDifferences_le v θ θ' hd)
  obtain ⟨n₁, hn₁⟩ := hunif w hwmem
  have hopen := rightTranslate_center_sub_smul_mem_of_vanishing v θ θ' hwmem hw (n₁ + 1) (by omega)
    (level_succ v n₁ hn₁) c hc
  have hsq : ((gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) -
      μ • (1 : Module.End ℂ (LocalGL3 v → ℂ))) ^ 2) f =
      (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) w - μ • w) +
        (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) d - μ • d) := by
    simp only [hw_def, pow_two, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_smul, smul_sub]
    abel
  rw [hsq]
  exact Submodule.add_mem _ hopen (Submodule.sub_mem _ (rightTranslate_center_mem_radicalDifferences v θ θ' c hd)
    (Submodule.smul_mem _ _ hd))

private theorem annihilator_sq_mem (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hunif : ∀ f : LocalGL3 v → ℂ, f ∈ principalSeries3 v ![θ, θ, θ'] →
      ∃ n : ℕ, ∀ k : LocalGL3 v,
        (∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
            ≤ WithZero.exp (-(n : ℤ))) →
        gl3AmbientRightTranslate (R := ℂ) k f = f)
    (c : (v.adicCompletion ℚ)ˣ) {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v ![θ, θ, θ'])
    (hP : ∀ g : LocalGL3 v, gl3Entry v g 2 0 = 0 → gl3Entry v g 2 1 = 0 → f g = 0) :
    ((gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) -
        (((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) • (1 : Module.End ℂ (LocalGL3 v → ℂ))) ^ 2) f ∈
      radicalDifferences v θ θ' := by
  by_cases hc : Valued.v (c : v.adicCompletion ℚ) ≤ 1
  · exact annihilator_sq_mem_of_valued_le_one v θ θ' hunif c hc hf hP

  have hc' : Valued.v ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_le_one_of_one_le₀ (not_le.mp hc).le
  have h₁ := annihilator_sq_mem_of_valued_le_one v θ θ' hunif c⁻¹ hc' hf hP

  have hzz : diagonal3 v ![1, 1, c] * diagonal3 v ![1, 1, c⁻¹] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal, diagonal3_coe, Units.ne_zero]

  have hθ0 : ((θ c : ℂˣ) : ℂ) ≠ 0 := (θ c).ne_zero
  have hN0 : ((‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr c.ne_zero)

  have key : ((gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) -
      (((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) • (1 : Module.End ℂ (LocalGL3 v → ℂ))) ^ 2) f =
      ((((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) ^ 2) •
        gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c])
          (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c])
            (((gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c⁻¹]) -
              (((θ c⁻¹ : ℂˣ) : ℂ) * (((‖((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) •
                (1 : Module.End ℂ (LocalGL3 v → ℂ))) ^ 2) f)) := by
    funext g
    simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul, gl3AmbientRightTranslate_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_assoc,
      hzz, mul_one, map_inv, Units.val_inv_eq_inv_val, norm_inv, inv_inv, Complex.ofReal_inv]
    field_simp
    ring
  rw [key]
  exact Submodule.smul_mem _ _ (rightTranslate_center_mem_radicalDifferences v θ θ' c
    (rightTranslate_center_mem_radicalDifferences v θ θ' c h₁))

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

private theorem annihilator_sq_mem_span_radicalDifferences
    (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hunif : ∀ f : LocalGL3 v → ℂ, f ∈ principalSeries3 v ![θ, θ, θ'] →
      ∃ n : ℕ, ∀ k : LocalGL3 v,
        (∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
            ≤ WithZero.exp (-(n : ℤ))) →
        gl3AmbientRightTranslate (R := ℂ) k f = f)
    :
    ∀ (c : (v.adicCompletion ℚ)ˣ) (f : LocalGL3 v → ℂ), f ∈ principalSeries3 v ![θ, θ, θ'] →
        (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) →
        ((gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) -
            (((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) •
              (1 : Module.End ℂ (LocalGL3 v → ℂ))) ^ 2) f ∈
          Submodule.span ℂ {d : LocalGL3 v → ℂ | ∃ (n : LocalGL3 v) (f' : LocalGL3 v → ℂ),
            f' ∈ principalSeries3 v ![θ, θ, θ'] ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = 1 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 = 1 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = 1 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 = 0 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧
            d = gl3AmbientRightTranslate (R := ℂ) n f' - f'} := by
  intro c f hf hP
  exact annihilator_sq_mem v θ θ' hunif c hf fun g h0 h1 => hP g h0 h1

end LanglandsTunnell.CubicInduction.ParabolicCharts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace PrincipalSeriesPermutation
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private noncomputable def leviNorm (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) : ℂ :=
  ((‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ)

private noncomputable def restrictFn (v : HeightOneSpectrum (𝓞 ℚ))
    (f : LocalGL3 v → ℂ) (m : GL (Fin 2) (v.adicCompletion ℚ)) : ℂ :=
  leviNorm v m * f (iotaGL m)

private theorem det_norm_pos (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    0 < ‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ :=
  norm_pos_iff.mpr ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit m)).ne_zero

private theorem leviNorm_mul (v : HeightOneSpectrum (𝓞 ℚ)) (m A : GL (Fin 2) (v.adicCompletion ℚ)) :
    leviNorm v (m * A) =
      leviNorm v m * ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) := by
  unfold leviNorm
  rw [Units.val_mul, Matrix.det_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_mul]

private theorem det_rpow_half_mul_neg_half (v : HeightOneSpectrum (𝓞 ℚ)) (A : GL (Fin 2) (v.adicCompletion ℚ)) :
    ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
        ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Real.rpow_add (det_norm_pos v A), add_neg_cancel, Real.rpow_zero, Complex.ofReal_one]

private theorem exists_radical_mul_of_block (v : HeightOneSpectrum (𝓞 ℚ))
    (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ))
    (c : (v.adicCompletion ℚ)ˣ)
    (h20 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0)
    (h22 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ))
    (hblock : ∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) :
    ∃ y z : v.adicCompletion ℚ, p = upperUnipotent3 0 y z * (iotaGL A * diagonal3 v ![1, 1, c]) := by
  have h00 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 := hblock 0 0
  have h01 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 := hblock 0 1
  have h10 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 := hblock 1 0
  have h11 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 := hblock 1 1
  refine ⟨(p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2 * ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ),
    (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2 * ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ),
    Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, upperUnipotent3_coe, coe_iotaGL, diagonal3_coe]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.diagonal, h00, h01, h10, h11, h20, h21, h22]

private theorem iotaGL_mul_radical (v : HeightOneSpectrum (𝓞 ℚ))
    (m : GL (Fin 2) (v.adicCompletion ℚ)) (y z : v.adicCompletion ℚ) :
    iotaGL m * upperUnipotent3 0 y z =
      upperUnipotent3 0
        ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 * z +
          (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 * y)
        ((m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 * z +
          (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 * y) * iotaGL m := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, upperUnipotent3_coe, upperUnipotent3_coe, coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem iotaGL_mul_center (v : HeightOneSpectrum (𝓞 ℚ))
    (m : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ) :
    iotaGL m * diagonal3 v ![1, 1, c] = diagonal3 v ![1, 1, c] * iotaGL m := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_iotaGL, diagonal3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Matrix.diagonal]

private theorem torusChar3_center (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (c : (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ ![1, 1, c] = ((χ 2 c : ℂˣ) : ℂ) := by
  simp [torusChar3, Fin.prod_univ_three]

private theorem halfModulus3_center (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v ![1, 1, c] = ((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) := by
  simp [halfModulus3]

private theorem restrictFn_rightTranslate (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ))
    (c : (v.adicCompletion ℚ)ˣ)
    (h20 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0)
    (h22 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ))
    (hblock : ∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j)
    (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    restrictFn v (gl3AmbientRightTranslate (R := ℂ) p f) m =
      ((χ 2 c : ℂˣ) : ℂ) * ((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) *
        ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
        restrictFn v f (m * A) := by
  obtain ⟨y, z, hp⟩ := exists_radical_mul_of_block v p A c h20 h21 h22 hblock
  simp only [restrictFn, gl3AmbientRightTranslate_apply]
  rw [hp, ← mul_assoc (iotaGL m), iotaGL_mul_radical, mul_assoc,
    apply_upperUnipotent3_mul_of_mem_principalSeries3 hf, ← mul_assoc, ← map_mul, iotaGL_mul_center,
    apply_diagonal3_mul_of_mem_principalSeries3 hf, torusChar3_center, halfModulus3_center, leviNorm_mul]
  have hdet := det_rpow_half_mul_neg_half v A
  generalize ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) = Dp at hdet ⊢
  generalize ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) = Dm at hdet ⊢
  linear_combination (-(leviNorm v m * ((χ 2 c : ℂˣ) : ℂ) * ((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) *
    f (iotaGL (m * A)))) * hdet

private theorem iotaGL_eq_upperUnipotent3_of_unipotent (v : HeightOneSpectrum (𝓞 ℚ))
    (u : GL (Fin 2) (v.adicCompletion ℚ))
    (hu00 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 = 1)
    (hu11 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1)
    (hu10 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0) :
    iotaGL u = upperUnipotent3 ((u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) 0 0 := by
  apply Units.ext
  rw [coe_iotaGL, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, hu00, hu11, hu10]

private theorem det_eq_one_of_unipotent (v : HeightOneSpectrum (𝓞 ℚ)) (u : GL (Fin 2) (v.adicCompletion ℚ))
    (hu00 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 = 1)
    (hu11 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1)
    (hu10 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0) :
    (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
  rw [Matrix.det_fin_two, hu00, hu11, hu10]
  ring

private theorem restrictFn_unipotent_mul (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (u : GL (Fin 2) (v.adicCompletion ℚ))
    (hu00 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 = 1)
    (hu11 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1)
    (hu10 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0)
    (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    restrictFn v f (u * m) = restrictFn v f m := by
  unfold restrictFn
  rw [map_mul, iotaGL_eq_upperUnipotent3_of_unipotent v u hu00 hu11 hu10,
    apply_upperUnipotent3_mul_of_mem_principalSeries3 hf]
  congr 1
  unfold leviNorm
  rw [Units.val_mul, Matrix.det_mul, det_eq_one_of_unipotent v u hu00 hu11 hu10, one_mul]

private theorem iotaGL_eq_diagonal3_of_diagonal (v : HeightOneSpectrum (𝓞 ℚ)) (d : GL (Fin 2) (v.adicCompletion ℚ))
    (a₀ a₁ : (v.adicCompletion ℚ)ˣ)
    (hd : (d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(a₀ : v.adicCompletion ℚ), (a₁ : v.adicCompletion ℚ)]) :
    iotaGL d = diagonal3 v ![a₀, a₁, 1] := by
  apply Units.ext
  rw [coe_iotaGL, diagonal3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, hd, Matrix.diagonal]

private theorem torusChar3_diagonal (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a₀ a₁ : (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ ![a₀, a₁, 1] = ((χ 0 a₀ : ℂˣ) : ℂ) * ((χ 1 a₁ : ℂˣ) : ℂ) := by
  simp [torusChar3, Fin.prod_univ_three]

private theorem halfModulus3_diagonal (v : HeightOneSpectrum (𝓞 ℚ)) (a₀ a₁ : (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v ![a₀, a₁, 1] = ((‖(a₀ : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
  simp [halfModulus3]

private theorem mul_rpow_neg_half_eq_sqrt_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * (x * y) ^ (-((1 : ℝ) / 2)) = Real.sqrt (x / y) := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow hx.le hy.le, Real.mul_rpow hx.le hy.le, Real.rpow_neg hx.le,
    Real.rpow_neg hy.le]
  have hx2 : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
    rw [← Real.rpow_add hx]
    norm_num
  have ha0 : x ^ ((1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  set a := x ^ ((1 : ℝ) / 2)
  rw [← hx2, div_eq_mul_inv a, mul_mul_mul_comm, mul_inv_cancel₀ ha0, one_mul]

private theorem restrictFn_diagonal_mul (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (d : GL (Fin 2) (v.adicCompletion ℚ)) (a₀ a₁ : (v.adicCompletion ℚ)ˣ)
    (hd : (d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(a₀ : v.adicCompletion ℚ), (a₁ : v.adicCompletion ℚ)])
    (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    restrictFn v f (d * m) =
      ((χ 0 a₀ : ℂˣ) : ℂ) * ((χ 1 a₁ : ℂˣ) : ℂ) *
        ((Real.sqrt (‖(a₀ : v.adicCompletion ℚ)‖ / ‖(a₁ : v.adicCompletion ℚ)‖) : ℝ) : ℂ) * restrictFn v f m := by
  unfold restrictFn
  rw [map_mul, iotaGL_eq_diagonal3_of_diagonal v d a₀ a₁ hd, apply_diagonal3_mul_of_mem_principalSeries3 hf,
    torusChar3_diagonal, halfModulus3_diagonal]
  have hsplit : leviNorm v (d * m) =
      ((‖(d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) * leviNorm v m := by
    unfold leviNorm
    rw [Units.val_mul, Matrix.det_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_mul]
  have hdet : (d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det =
      (a₀ : v.adicCompletion ℚ) * (a₁ : v.adicCompletion ℚ) := by
    rw [hd, Matrix.det_fin_two]
    simp
  have hkey : ((‖(a₀ : v.adicCompletion ℚ)‖ : ℝ) : ℂ) *
      ((‖(d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) =
      ((Real.sqrt (‖(a₀ : v.adicCompletion ℚ)‖ / ‖(a₁ : v.adicCompletion ℚ)‖) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hdet, norm_mul,
      mul_rpow_neg_half_eq_sqrt_div (norm_pos_iff.mpr a₀.ne_zero) (norm_pos_iff.mpr a₁.ne_zero)]
  rw [hsplit, ← hkey]
  ring

private theorem continuous_iotaGL (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous (iotaGL : GL (Fin 2) (v.adicCompletion ℚ) →* LocalGL3 v) := by
  rw [Units.continuous_iff]
  constructor
  · apply continuous_matrix
    intro i j
    simp only [Function.comp_apply, coe_iotaGL, embedMat2]
    fin_cases i <;> fin_cases j <;>
      first
      | exact continuous_const
      | exact Units.continuous_val.matrix_elem 0 0
      | exact Units.continuous_val.matrix_elem 0 1
      | exact Units.continuous_val.matrix_elem 1 0
      | exact Units.continuous_val.matrix_elem 1 1
  · apply continuous_matrix
    intro i j
    simp only [← map_inv, coe_iotaGL, embedMat2]
    fin_cases i <;> fin_cases j <;>
      first
      | exact continuous_const
      | exact Units.continuous_coe_inv.matrix_elem 0 0
      | exact Units.continuous_coe_inv.matrix_elem 0 1
      | exact Units.continuous_coe_inv.matrix_elem 1 0
      | exact Units.continuous_coe_inv.matrix_elem 1 1

private theorem isLocallyConstant_leviNorm (v : HeightOneSpectrum (𝓞 ℚ)) : IsLocallyConstant (leviNorm v) := by
  have hnorm : IsLocallyConstant fun m : GL (Fin 2) (v.adicCompletion ℚ) =>
      ‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro m
    have hc : ContinuousAt (fun m : GL (Fin 2) (v.adicCompletion ℚ) =>
        (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det) m :=
      (Units.continuous_val.matrix_det).continuousAt
    exact hc.eventually (eventually_norm_eq v ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit m)).ne_zero)
  exact hnorm.comp fun r : ℝ => ((r ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ)

private theorem isLocallyConstant_restrictFn (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) : IsLocallyConstant (restrictFn v f) :=
  (isLocallyConstant_leviNorm v).mul
    ((isLocallyConstant_of_mem_principalSeries3 hf).comp_continuous (continuous_iotaGL v))

end LanglandsTunnell.CubicInduction.PrincipalSeriesPermutation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace PrincipalSeriesPermutation
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private noncomputable def embedLow (v : HeightOneSpectrum (𝓞 ℚ)) (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ) :=
  !![1, 0, 0; 0, M 0 0, M 0 1; 0, M 1 0, M 1 1]

private theorem embedLow_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    embedLow v (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedLow]

private theorem embedLow_mul (v : HeightOneSpectrum (𝓞 ℚ)) (M N : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    embedLow v (M * N) = embedLow v M * embedLow v N := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [embedLow, Matrix.mul_apply, Fin.sum_univ_two]

private noncomputable def iotaLow (v : HeightOneSpectrum (𝓞 ℚ)) :
    GL (Fin 2) (v.adicCompletion ℚ) →* GL (Fin 3) (v.adicCompletion ℚ) where
  toFun h :=
    { val := embedLow v h
      inv := embedLow v ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
      val_inv := by rw [← embedLow_mul, Units.mul_inv, embedLow_one]
      inv_val := by rw [← embedLow_mul, Units.inv_mul, embedLow_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact embedLow_one v)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact embedLow_mul v _ _)

private theorem coe_iotaLow (v : HeightOneSpectrum (𝓞 ℚ)) (h : GL (Fin 2) (v.adicCompletion ℚ)) :
    ((iotaLow v h : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      embedLow v (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := rfl

private noncomputable def leviNormLow (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) : ℂ :=
  ((‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ)

private noncomputable def restrictLowFn (v : HeightOneSpectrum (𝓞 ℚ))
    (f : LocalGL3 v → ℂ) (m : GL (Fin 2) (v.adicCompletion ℚ)) : ℂ :=
  leviNormLow v m * f (iotaLow v m)

private theorem leviNormLow_mul (v : HeightOneSpectrum (𝓞 ℚ)) (m A : GL (Fin 2) (v.adicCompletion ℚ)) :
    leviNormLow v (m * A) =
      leviNormLow v m * ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
  unfold leviNormLow
  rw [Units.val_mul, Matrix.det_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_mul]

private theorem exists_center_mul_of_lowBlock (v : HeightOneSpectrum (𝓞 ℚ))
    (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ))
    (c : (v.adicCompletion ℚ)ˣ)
    (h00 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = (c : v.adicCompletion ℚ))
    (h10 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0)
    (h20 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (hblock : ∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.succ i) (Fin.succ j)
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) :
    ∃ x z : v.adicCompletion ℚ, p = diagonal3 v ![c, 1, 1] * (iotaLow v A * upperUnipotent3 x 0 z) := by
  have h11 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 := hblock 0 0
  have h12 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 := hblock 0 1
  have h21 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 := hblock 1 0
  have h22 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 := hblock 1 1
  refine ⟨((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1,
    ((c⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 2,
    Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, diagonal3_coe, coe_iotaLow, upperUnipotent3_coe]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [embedLow, Matrix.diagonal, h00, h10, h20, h11, h12, h21, h22]

private theorem radical_mul_iotaLow (v : HeightOneSpectrum (𝓞 ℚ)) (x z : v.adicCompletion ℚ)
    (B : GL (Fin 2) (v.adicCompletion ℚ)) :
    upperUnipotent3 x 0 z * iotaLow v B =
      iotaLow v B *
        upperUnipotent3
          (x * (B : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 +
            z * (B : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0) 0
          (x * (B : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 +
            z * (B : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, upperUnipotent3_coe, upperUnipotent3_coe, coe_iotaLow]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [embedLow]

private theorem exists_iotaLow_mul_radical (v : HeightOneSpectrum (𝓞 ℚ)) (B : GL (Fin 2) (v.adicCompletion ℚ))
    (x z : v.adicCompletion ℚ) :
    ∃ x' z' : v.adicCompletion ℚ, iotaLow v B * upperUnipotent3 x 0 z = upperUnipotent3 x' 0 z' * iotaLow v B := by
  obtain ⟨x', z', h⟩ : ∃ x' z' : v.adicCompletion ℚ,
      upperUnipotent3 x 0 z * iotaLow v B⁻¹ = iotaLow v B⁻¹ * upperUnipotent3 x' 0 z' :=
    ⟨_, _, radical_mul_iotaLow v x z B⁻¹⟩
  refine ⟨x', z', ?_⟩
  calc iotaLow v B * upperUnipotent3 x 0 z
      = iotaLow v B * (upperUnipotent3 x 0 z * iotaLow v B⁻¹) * iotaLow v B := by
        rw [mul_assoc, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    _ = iotaLow v B * (iotaLow v B⁻¹ * upperUnipotent3 x' 0 z') * iotaLow v B := by rw [h]
    _ = upperUnipotent3 x' 0 z' * iotaLow v B := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

private theorem iotaLow_mul_center (v : HeightOneSpectrum (𝓞 ℚ))
    (m : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ) :
    iotaLow v m * diagonal3 v ![c, 1, 1] = diagonal3 v ![c, 1, 1] * iotaLow v m := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_iotaLow, diagonal3_coe]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [embedLow, Matrix.diagonal]

private theorem torusChar3_lowCenter (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (c : (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ ![c, 1, 1] = ((χ 0 c : ℂˣ) : ℂ) := by
  simp [torusChar3, Fin.prod_univ_three]

private theorem halfModulus3_lowCenter (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v ![c, 1, 1] = ((‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
  simp [halfModulus3]

private theorem restrictLowFn_rightTranslate (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ))
    (c : (v.adicCompletion ℚ)ˣ)
    (h00 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = (c : v.adicCompletion ℚ))
    (h10 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0)
    (h20 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (hblock : ∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.succ i) (Fin.succ j)
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j)
    (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    restrictLowFn v (gl3AmbientRightTranslate (R := ℂ) p f) m =
      ((χ 0 c : ℂˣ) : ℂ) * ((‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) *
        ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) *
        restrictLowFn v f (m * A) := by
  obtain ⟨x, z, hp⟩ := exists_center_mul_of_lowBlock v p A c h00 h10 h20 hblock
  obtain ⟨x', z', hconj⟩ := exists_iotaLow_mul_radical v (m * A) x z
  simp only [restrictLowFn, gl3AmbientRightTranslate_apply]
  rw [hp, ← mul_assoc (iotaLow v m), iotaLow_mul_center, mul_assoc, apply_diagonal3_mul_of_mem_principalSeries3 hf,
    torusChar3_lowCenter, halfModulus3_lowCenter, ← mul_assoc (iotaLow v m), ← map_mul, hconj,
    apply_upperUnipotent3_mul_of_mem_principalSeries3 hf, leviNormLow_mul]
  have hdet := det_rpow_half_mul_neg_half v A
  generalize ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) = Dp at hdet ⊢
  generalize ((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) = Dm at hdet ⊢
  linear_combination (-(leviNormLow v m * ((χ 0 c : ℂˣ) : ℂ) * ((‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) *
    f (iotaLow v (m * A)))) * hdet

private theorem iotaLow_eq_upperUnipotent3_of_unipotent (v : HeightOneSpectrum (𝓞 ℚ))
    (u : GL (Fin 2) (v.adicCompletion ℚ))
    (hu00 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 = 1)
    (hu11 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1)
    (hu10 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0) :
    iotaLow v u = upperUnipotent3 0 ((u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) 0 := by
  apply Units.ext
  rw [coe_iotaLow, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedLow, hu00, hu11, hu10]

private theorem restrictLowFn_unipotent_mul (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (u : GL (Fin 2) (v.adicCompletion ℚ))
    (hu00 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0 = 1)
    (hu11 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 = 1)
    (hu10 : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0)
    (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    restrictLowFn v f (u * m) = restrictLowFn v f m := by
  unfold restrictLowFn
  rw [map_mul, iotaLow_eq_upperUnipotent3_of_unipotent v u hu00 hu11 hu10,
    apply_upperUnipotent3_mul_of_mem_principalSeries3 hf]
  congr 1
  unfold leviNormLow
  rw [Units.val_mul, Matrix.det_mul, det_eq_one_of_unipotent v u hu00 hu11 hu10, one_mul]

private theorem iotaLow_eq_diagonal3_of_diagonal (v : HeightOneSpectrum (𝓞 ℚ)) (d : GL (Fin 2) (v.adicCompletion ℚ))
    (b₀ b₁ : (v.adicCompletion ℚ)ˣ)
    (hd : (d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(b₀ : v.adicCompletion ℚ), (b₁ : v.adicCompletion ℚ)]) :
    iotaLow v d = diagonal3 v ![1, b₀, b₁] := by
  apply Units.ext
  rw [coe_iotaLow, diagonal3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedLow, hd, Matrix.diagonal]

private theorem torusChar3_lowDiagonal (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (b₀ b₁ : (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ ![1, b₀, b₁] = ((χ 1 b₀ : ℂˣ) : ℂ) * ((χ 2 b₁ : ℂˣ) : ℂ) := by
  simp [torusChar3, Fin.prod_univ_three]

private theorem halfModulus3_lowDiagonal (v : HeightOneSpectrum (𝓞 ℚ)) (b₀ b₁ : (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v ![1, b₀, b₁] = ((‖(b₁ : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) := by
  simp [halfModulus3]

private theorem inv_mul_rpow_half_eq_sqrt_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    y⁻¹ * (x * y) ^ ((1 : ℝ) / 2) = Real.sqrt (x / y) := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow hx.le hy.le, Real.mul_rpow hx.le hy.le]
  have hy2 : y ^ ((1 : ℝ) / 2) * y ^ ((1 : ℝ) / 2) = y := by
    rw [← Real.rpow_add hy]
    norm_num
  have hb0 : y ^ ((1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
  set a := x ^ ((1 : ℝ) / 2)
  set b := y ^ ((1 : ℝ) / 2)
  rw [← hy2, mul_inv, div_eq_mul_inv a b, mul_mul_mul_comm, inv_mul_cancel₀ hb0, mul_one, mul_comm b⁻¹ a]

private theorem restrictLowFn_diagonal_mul (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (d : GL (Fin 2) (v.adicCompletion ℚ)) (b₀ b₁ : (v.adicCompletion ℚ)ˣ)
    (hd : (d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(b₀ : v.adicCompletion ℚ), (b₁ : v.adicCompletion ℚ)])
    (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    restrictLowFn v f (d * m) =
      ((χ 1 b₀ : ℂˣ) : ℂ) * ((χ 2 b₁ : ℂˣ) : ℂ) *
        ((Real.sqrt (‖(b₀ : v.adicCompletion ℚ)‖ / ‖(b₁ : v.adicCompletion ℚ)‖) : ℝ) : ℂ) *
        restrictLowFn v f m := by
  unfold restrictLowFn
  rw [map_mul, iotaLow_eq_diagonal3_of_diagonal v d b₀ b₁ hd, apply_diagonal3_mul_of_mem_principalSeries3 hf,
    torusChar3_lowDiagonal, halfModulus3_lowDiagonal]
  have hsplit : leviNormLow v (d * m) =
      ((‖(d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * leviNormLow v m := by
    unfold leviNormLow
    rw [Units.val_mul, Matrix.det_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Complex.ofReal_mul]
  have hdet : (d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det =
      (b₀ : v.adicCompletion ℚ) * (b₁ : v.adicCompletion ℚ) := by
    rw [hd, Matrix.det_fin_two]
    simp
  have hkey : ((‖(b₁ : v.adicCompletion ℚ)‖⁻¹ : ℝ) : ℂ) *
      ((‖(d : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) =
      ((Real.sqrt (‖(b₀ : v.adicCompletion ℚ)‖ / ‖(b₁ : v.adicCompletion ℚ)‖) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hdet, norm_mul,
      inv_mul_rpow_half_eq_sqrt_div (norm_pos_iff.mpr b₀.ne_zero) (norm_pos_iff.mpr b₁.ne_zero)]
  rw [hsplit, ← hkey]
  ring

private theorem continuous_iotaLow (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous (iotaLow v : GL (Fin 2) (v.adicCompletion ℚ) →* LocalGL3 v) := by
  rw [Units.continuous_iff]
  constructor
  · apply continuous_matrix
    intro i j
    simp only [Function.comp_apply, coe_iotaLow, embedLow]
    fin_cases i <;> fin_cases j <;>
      first
      | exact continuous_const
      | exact Units.continuous_val.matrix_elem 0 0
      | exact Units.continuous_val.matrix_elem 0 1
      | exact Units.continuous_val.matrix_elem 1 0
      | exact Units.continuous_val.matrix_elem 1 1
  · apply continuous_matrix
    intro i j
    simp only [← map_inv, coe_iotaLow, embedLow]
    fin_cases i <;> fin_cases j <;>
      first
      | exact continuous_const
      | exact Units.continuous_coe_inv.matrix_elem 0 0
      | exact Units.continuous_coe_inv.matrix_elem 0 1
      | exact Units.continuous_coe_inv.matrix_elem 1 0
      | exact Units.continuous_coe_inv.matrix_elem 1 1

private theorem isLocallyConstant_leviNormLow (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsLocallyConstant (leviNormLow v) := by
  have hnorm : IsLocallyConstant fun m : GL (Fin 2) (v.adicCompletion ℚ) =>
      ‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro m
    have hc : ContinuousAt (fun m : GL (Fin 2) (v.adicCompletion ℚ) =>
        (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det) m :=
      (Units.continuous_val.matrix_det).continuousAt
    exact hc.eventually (eventually_norm_eq v ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit m)).ne_zero)
  exact hnorm.comp fun r : ℝ => ((r ^ ((1 : ℝ) / 2) : ℝ) : ℂ)

private theorem isLocallyConstant_restrictLowFn (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) : IsLocallyConstant (restrictLowFn v f) :=
  (isLocallyConstant_leviNormLow v).mul
    ((isLocallyConstant_of_mem_principalSeries3 hf).comp_continuous (continuous_iotaLow v))

end LanglandsTunnell.CubicInduction.PrincipalSeriesPermutation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace PrincipalSeriesPermutation
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private theorem restrictFn_add (v : HeightOneSpectrum (𝓞 ℚ)) (f g : LocalGL3 v → ℂ) :
    restrictFn v (f + g) = restrictFn v f + restrictFn v g := by
  funext m
  simp only [restrictFn, Pi.add_apply]
  ring

private theorem restrictFn_smul (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℂ) (f : LocalGL3 v → ℂ) :
    restrictFn v (a • f) = a • restrictFn v f := by
  funext m
  simp only [restrictFn, Pi.smul_apply, smul_eq_mul]
  ring

private theorem restrictLowFn_add (v : HeightOneSpectrum (𝓞 ℚ)) (f g : LocalGL3 v → ℂ) :
    restrictLowFn v (f + g) = restrictLowFn v f + restrictLowFn v g := by
  funext m
  simp only [restrictLowFn, Pi.add_apply]
  ring

private theorem restrictLowFn_smul (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℂ) (f : LocalGL3 v → ℂ) :
    restrictLowFn v (a • f) = a • restrictLowFn v f := by
  funext m
  simp only [restrictLowFn, Pi.smul_apply, smul_eq_mul]
  ring

private theorem diagonal2_coe_pair (v : HeightOneSpectrum (𝓞 ℚ)) (a : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    (diagonal2 v a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![(a 0 : v.adicCompletion ℚ), (a 1 : v.adicCompletion ℚ)] := by
  rw [diagonal2_coe]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem restrictFn_mem (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) : restrictFn v f ∈ principalSeries2 v ![χ 0, χ 1] := by
  refine ⟨isLocallyConstant_restrictFn v χ hf, fun x m => ?_, fun a m => ?_⟩
  · exact restrictFn_unipotent_mul v χ hf (upperUnipotent2 v x) (by simp) (by simp) (by simp) m
  · rw [restrictFn_diagonal_mul v χ hf (diagonal2 v a) (a 0) (a 1) (diagonal2_coe_pair v a) m]
    simp only [torusChar2, halfModulus2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem restrictLowFn_mem (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) : restrictLowFn v f ∈ principalSeries2 v ![χ 1, χ 2] := by
  refine ⟨isLocallyConstant_restrictLowFn v χ hf, fun x m => ?_, fun a m => ?_⟩
  · exact restrictLowFn_unipotent_mul v χ hf (upperUnipotent2 v x) (by simp) (by simp) (by simp) m
  · rw [restrictLowFn_diagonal_mul v χ hf (diagonal2 v a) (a 0) (a 1) (diagonal2_coe_pair v a) m]
    simp only [torusChar2, halfModulus2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

private noncomputable def restrictLin (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries2 v ![χ 0, χ 1]) where
  toFun f := ⟨restrictFn v f, restrictFn_mem v χ f.2⟩
  map_add' f g := by
    ext m
    simp only [Submodule.coe_add, restrictFn_add, Pi.add_apply]
  map_smul' a f := by
    ext m
    simp only [Submodule.coe_smul, restrictFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

private noncomputable def restrictLowLin (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries2 v ![χ 1, χ 2]) where
  toFun f := ⟨restrictLowFn v f, restrictLowFn_mem v χ f.2⟩
  map_add' f g := by
    ext m
    simp only [Submodule.coe_add, restrictLowFn_add, Pi.add_apply]
  map_smul' a f := by
    ext m
    simp only [Submodule.coe_smul, restrictLowFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

private theorem restrictLin_apply_coe (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : ↥(principalSeries3 v χ)) :
    ((restrictLin v χ f : ↥(principalSeries2 v ![χ 0, χ 1])) : LocalGL2 v → ℂ) = restrictFn v f := rfl

private theorem restrictLowLin_apply_coe (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : ↥(principalSeries3 v χ)) :
    ((restrictLowLin v χ f : ↥(principalSeries2 v ![χ 1, χ 2])) : LocalGL2 v → ℂ) = restrictLowFn v f := rfl

private theorem restrictLin_apply_of_det_eq_one (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (f : ↥(principalSeries3 v χ)) (m : GL (Fin 2) (v.adicCompletion ℚ))
    (hm : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1) :
    ((restrictLin v χ f : ↥(principalSeries2 v ![χ 0, χ 1])) : LocalGL2 v → ℂ) m =
      (f : LocalGL3 v → ℂ) (iotaGL m) := by
  rw [restrictLin_apply_coe]
  unfold restrictFn leviNorm
  rw [hm, norm_one, Real.one_rpow, Complex.ofReal_one, one_mul]

private theorem restrictLowLin_apply_of_det_eq_one (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (f : ↥(principalSeries3 v χ)) (m : GL (Fin 2) (v.adicCompletion ℚ))
    (hm : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1) :
    ((restrictLowLin v χ f : ↥(principalSeries2 v ![χ 1, χ 2])) : LocalGL2 v → ℂ) m =
      (f : LocalGL3 v → ℂ) (iotaLow v m) := by
  rw [restrictLowLin_apply_coe]
  unfold restrictLowFn leviNormLow
  rw [hm, norm_one, Real.one_rpow, Complex.ofReal_one, one_mul]

private theorem principalSeries2Rep_apply_coe (v : HeightOneSpectrum (𝓞 ℚ))
    (ψ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (A : LocalGL2 v) (φ : ↥(principalSeries2 v ψ)) (m : LocalGL2 v) :
    ((principalSeries2Rep (v := v) ψ A φ : ↥(principalSeries2 v ψ)) : LocalGL2 v → ℂ) m =
      (φ : LocalGL2 v → ℂ) (m * A) := rfl

private theorem restrictLin_rightTranslate (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ)
    (f : ↥(principalSeries3 v χ))
    (h20 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0)
    (h22 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ))
    (hblock : ∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) :
    restrictLin v χ ⟨gl3AmbientRightTranslate (R := ℂ) p f, rightTranslate_mem_principalSeries3 f.2 p⟩
      = ((((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2)) /
          ‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) •
        (((χ 2 c : ℂˣ) : ℂ) • (principalSeries2Rep (v := v) ![χ 0, χ 1]) A (restrictLin v χ f))) := by
  ext m
  rw [restrictLin_apply_coe, Submodule.coe_smul, Pi.smul_apply, Submodule.coe_smul, Pi.smul_apply,
    principalSeries2Rep_apply_coe, restrictLin_apply_coe,
    restrictFn_rightTranslate v χ f.2 p A c h20 h21 h22 hblock m, smul_eq_mul, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_inv]
  ring

private theorem restrictLowLin_rightTranslate (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ)
    (f : ↥(principalSeries3 v χ))
    (h00 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = (c : v.adicCompletion ℚ))
    (h10 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0)
    (h20 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0)
    (hblock : ∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.succ i) (Fin.succ j)
      = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) :
    restrictLowLin v χ ⟨gl3AmbientRightTranslate (R := ℂ) p f, rightTranslate_mem_principalSeries3 f.2 p⟩
      = (((‖(c : v.adicCompletion ℚ)‖ *
          ‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) •
        (((χ 0 c : ℂˣ) : ℂ) • (principalSeries2Rep (v := v) ![χ 1, χ 2]) A (restrictLowLin v χ f))) := by
  ext m
  rw [restrictLowLin_apply_coe, Submodule.coe_smul, Pi.smul_apply, Submodule.coe_smul, Pi.smul_apply,
    principalSeries2Rep_apply_coe, restrictLowLin_apply_coe,
    restrictLowFn_rightTranslate v χ f.2 p A c h00 h10 h20 hblock m, smul_eq_mul, smul_eq_mul,
    Complex.ofReal_mul]
  ring

end LanglandsTunnell.CubicInduction.PrincipalSeriesPermutation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace PrincipalSeriesPermutation
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private theorem exists_forall_mem_higherUnits_eq_one (p : ℕ) [Fact p.Prime] (μ : ℚ_[p]ˣ →* ℂˣ)
    (hμ : IsLocallyConstant μ) : ∃ n : ℕ, ∀ u ∈ LocalNewvector.higherUnits p n, μ u = 1 := by
  have hopen : IsOpen {u : ℚ_[p]ˣ | μ u = 1} := by
    simpa only [map_one] using hμ.isOpen_fiber (μ 1)
  have himg : IsOpen ((Units.val : ℚ_[p]ˣ → ℚ_[p]) '' {u : ℚ_[p]ˣ | μ u = 1}) :=
    Units.isOpenEmbedding_val.isOpenMap _ hopen
  have hmem : (1 : ℚ_[p]) ∈ (Units.val : ℚ_[p]ˣ → ℚ_[p]) '' {u : ℚ_[p]ˣ | μ u = 1} :=
    ⟨1, map_one μ, Units.val_one⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp himg 1 hmem
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Nat.Prime.one_lt (Fact.out (p := p.Prime)))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp1)
  refine ⟨n + 1, fun u hu => ?_⟩
  obtain ⟨-, hu⟩ := hu
  rcases hu with h0 | hle
  · exact absurd h0 (Nat.succ_ne_zero n)
  have hlt : ‖(u : ℚ_[p]) - 1‖ < ε := by
    refine lt_of_le_of_lt hle ?_
    calc (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) = ((p : ℝ)⁻¹) ^ (n + 1) := by
          rw [zpow_neg, zpow_natCast, inv_pow]
      _ ≤ ((p : ℝ)⁻¹) ^ n :=
          pow_le_pow_of_le_one (inv_nonneg.mpr (Nat.cast_nonneg p)) (inv_le_one_of_one_le₀ hp1.le) (Nat.le_succ n)
      _ < ε := hn
  have hu' : (u : ℚ_[p]) ∈ Metric.ball (1 : ℚ_[p]) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hlt
  obtain ⟨u', hu'', huu'⟩ := hball hu'
  exact (Units.ext huu') ▸ hu''

private theorem exists_hasCharConductor_of_isLocallyConstant (p : ℕ) [Fact p.Prime] (μ : ℚ_[p]ˣ →* ℂˣ)
    (hμ : IsLocallyConstant μ) : ∃ c : ℕ, LocalNewvector.HasCharConductor p μ c := by
  classical
  have hlevel := exists_forall_mem_higherUnits_eq_one p μ hμ
  refine ⟨Nat.find hlevel, Nat.find_spec hlevel, fun m hm => ?_⟩
  by_contra hcon
  exact Nat.find_min hlevel hm fun u hu => by_contra fun hne => hcon ⟨u, hu, hne⟩

end LanglandsTunnell.CubicInduction.PrincipalSeriesPermutation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace LevelLattice
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private noncomputable def IsTransversal {G : Type*} [AddCommGroup G] (A' A : AddSubgroup G) (T : Finset G) : Prop :=
  (∀ p ∈ T, p ∈ A) ∧ (∀ a ∈ A, ∃ p ∈ T, a - p ∈ A') ∧ (∀ p ∈ T, ∀ p' ∈ T, p - p' ∈ A' → p = p')

private theorem isTransversal_of_finite {G : Type*} [AddCommGroup G] (A' A : AddSubgroup G)
    [Finite (A ⧸ A'.addSubgroupOf A)] :
    ∃ T : Finset G, IsTransversal A' A T ∧ T.card = Nat.card (A ⧸ A'.addSubgroupOf A) := by
  obtain ⟨T, h₁, h₂, h₃, h₄⟩ := exists_finset_transversal A' A
  exact ⟨T, ⟨h₁, h₂, h₃⟩, h₄⟩

private theorem sum_transversal_eq {G : Type*} [AddCommGroup G] {A' A : AddSubgroup G} {T T' : Finset G}
    (hT : IsTransversal A' A T) (hT' : IsTransversal A' A T') (φ : G → ℂ)
    (hφ : ∀ x : G, ∀ d ∈ A', φ (x + d) = φ x) : ∑ p ∈ T, φ p = ∑ p ∈ T', φ p := by
  have hex : ∀ p ∈ T, ∃ q ∈ T', p - q ∈ A' := fun p hp => hT'.2.1 p (hT.1 p hp)
  choose r hrT' hr using hex
  refine Finset.sum_bij r hrT' ?_ ?_ ?_
  · intro p₁ hp₁ p₂ hp₂ h
    apply hT.2.2 p₁ hp₁ p₂ hp₂
    have h₁ := hr p₁ hp₁
    have h₂ := hr p₂ hp₂
    rw [h] at h₁
    have := A'.sub_mem h₁ h₂
    rwa [sub_sub_sub_cancel_right] at this
  · intro q hq
    obtain ⟨p, hp, hpq⟩ := hT.2.1 q (hT'.1 q hq)
    refine ⟨p, hp, hT'.2.2 _ (hrT' p hp) q hq ?_⟩
    have := A'.sub_mem (A'.neg_mem (hr p hp)) hpq
    rwa [neg_sub, sub_sub_sub_cancel_right] at this
  · intro p hp
    have h₁ := hr p hp
    calc φ p = φ (r p hp + (p - r p hp)) := by congr 1; abel
      _ = φ (r p hp) := hφ _ _ h₁

private theorem count_eq_of_isTransversal {G : Type*} [AddCommGroup G] {A' A : AddSubgroup G} {T T' : Finset G}
    (hT : IsTransversal A' A T) (hT' : IsTransversal A' A T') : T.card = T'.card := by
  have h := sum_transversal_eq hT hT' (fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

private noncomputable def latticeSum {G : Type*} [AddCommGroup G] (A' A : AddSubgroup G) (w : ℝ) (φ : G → ℂ) : ℂ := by
  classical
  exact if h : ∃ T : Finset G, IsTransversal A' A T then (w : ℂ) * ∑ p ∈ h.choose, φ p else 0

private theorem latticeSum_eq_sum {G : Type*} [AddCommGroup G] {A' A : AddSubgroup G} (w : ℝ) {T : Finset G}
    (hT : IsTransversal A' A T) {φ : G → ℂ} (hφ : ∀ x : G, ∀ d ∈ A', φ (x + d) = φ x) :
    latticeSum A' A w φ = (w : ℂ) * ∑ p ∈ T, φ p := by
  have h : ∃ T : Finset G, IsTransversal A' A T := ⟨T, hT⟩
  unfold latticeSum
  rw [dif_pos h, sum_transversal_eq h.choose_spec hT φ hφ]

private theorem latticeSum_add {G : Type*} [AddCommGroup G] (A' A : AddSubgroup G) (w : ℝ) (φ ψ : G → ℂ) :
    latticeSum A' A w (φ + ψ) = latticeSum A' A w φ + latticeSum A' A w ψ := by
  unfold latticeSum
  split_ifs
  · simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
  · simp

private theorem latticeSum_smul {G : Type*} [AddCommGroup G] (A' A : AddSubgroup G) (w : ℝ) (z : ℂ) (φ : G → ℂ) :
    latticeSum A' A w (fun x => z * φ x) = z * latticeSum A' A w φ := by
  unfold latticeSum
  split_ifs
  · rw [← Finset.mul_sum]
    ring
  · simp

private theorem latticeSum_congr {G : Type*} [AddCommGroup G] (A' A : AddSubgroup G) (w : ℝ) {φ ψ : G → ℂ}
    (h : ∀ x ∈ A, φ x = ψ x) : latticeSum A' A w φ = latticeSum A' A w ψ := by
  unfold latticeSum
  split_ifs with hT
  · congr 1
    exact Finset.sum_congr rfl fun p hp => h p (hT.choose_spec.1 p hp)
  · rfl

private theorem latticeSum_weight {G : Type*} [AddCommGroup G] (A' A : AddSubgroup G) (r w : ℝ) (φ : G → ℂ) :
    latticeSum A' A (r * w) φ = (r : ℂ) * latticeSum A' A w φ := by
  unfold latticeSum
  split_ifs
  · push_cast
    ring
  · simp

private theorem latticeSum_zero {G : Type*} [AddCommGroup G] (A' A : AddSubgroup G) (w : ℝ) :
    latticeSum A' A w (fun _ => (0 : ℂ)) = 0 := by
  unfold latticeSum
  split_ifs <;> simp

private theorem isTransversal_image_add {G : Type*} [AddCommGroup G] [DecidableEq G] {A' A : AddSubgroup G}
    {T : Finset G} (hT : IsTransversal A' A T) {y : G} (hy : y ∈ A) :
    IsTransversal A' A (T.image fun p => p + y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact A.add_mem (hT.1 p hp) hy
  · intro a ha
    obtain ⟨p, hp, hap⟩ := hT.2.1 (a - y) (A.sub_mem ha hy)
    refine ⟨p + y, Finset.mem_image_of_mem _ hp, ?_⟩
    rwa [sub_add_eq_sub_sub, sub_right_comm]
  · intro q hq q' hq' hqq'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hq'
    rw [add_sub_add_right_eq_sub] at hqq'
    rw [hT.2.2 p hp p' hp' hqq']

private theorem latticeSum_translate {G : Type*} [AddCommGroup G] {A' A : AddSubgroup G} (w : ℝ) {T : Finset G}
    (hT : IsTransversal A' A T) {φ : G → ℂ} (hφ : ∀ x : G, ∀ d ∈ A', φ (x + d) = φ x) {y : G} (hy : y ∈ A) :
    latticeSum A' A w (fun x => φ (x + y)) = latticeSum A' A w φ := by
  classical
  rw [latticeSum_eq_sum (φ := fun x => φ (x + y)) w hT
      (fun x d hd => by show φ (x + d + y) = φ (x + y); rw [add_right_comm, hφ _ _ hd]),
    latticeSum_eq_sum w (isTransversal_image_add hT hy) hφ,
    Finset.sum_image fun p _ p' _ h => add_right_cancel h]

private theorem refine_pairs_eq {G : Type*} [AddCommGroup G] {A'' A' A : AddSubgroup G} (hle : A'' ≤ A')
    {T S : Finset G} (hT : IsTransversal A' A T) (hS : IsTransversal A'' A' S) {t s t' s' : G} (ht : t ∈ T)
    (hs : s ∈ S) (ht' : t' ∈ T) (hs' : s' ∈ S) (h : t + s - (t' + s') ∈ A'') : t = t' ∧ s = s' := by
  have hss' : s - s' ∈ A' := A'.sub_mem (hS.1 s hs) (hS.1 s' hs')
  have htt' : t - t' ∈ A' := by
    have h' : t + s - (t' + s') = (t - t') + (s - s') := by abel
    rw [h'] at h
    simpa using A'.sub_mem (hle h) hss'
  have htt : t = t' := hT.2.2 t ht t' ht' htt'
  subst htt
  refine ⟨rfl, hS.2.2 s hs s' hs' ?_⟩
  simpa using h

private theorem isTransversal_refine {G : Type*} [AddCommGroup G] [DecidableEq G] {A'' A' A : AddSubgroup G}
    (hle : A'' ≤ A') (hle' : A' ≤ A) {T S : Finset G} (hT : IsTransversal A' A T) (hS : IsTransversal A'' A' S) :
    IsTransversal A'' A ((T ×ˢ S).image fun ts => ts.1 + ts.2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨⟨t, s⟩, hts, rfl⟩ := Finset.mem_image.mp hq
    rw [Finset.mem_product] at hts
    exact A.add_mem (hT.1 t hts.1) (hle' (hS.1 s hts.2))
  · intro a ha
    obtain ⟨t, ht, hat⟩ := hT.2.1 a ha
    obtain ⟨s, hs, has⟩ := hS.2.1 (a - t) hat
    refine ⟨t + s, Finset.mem_image_of_mem (fun ts : G × G => ts.1 + ts.2)
      (Finset.mem_product.mpr ⟨ht, hs⟩ : (t, s) ∈ T ×ˢ S), ?_⟩
    rwa [← sub_sub]
  · intro q hq q' hq' hqq'
    obtain ⟨⟨t, s⟩, hts, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨⟨t', s'⟩, hts', rfl⟩ := Finset.mem_image.mp hq'
    rw [Finset.mem_product] at hts hts'
    obtain ⟨rfl, rfl⟩ := refine_pairs_eq hle hT hS hts.1 hts.2 hts'.1 hts'.2 hqq'
    rfl

private theorem latticeSum_refine {G : Type*} [AddCommGroup G] {A'' A' A : AddSubgroup G} (hle : A'' ≤ A')
    (hle' : A' ≤ A) (w : ℝ) {T S : Finset G} (hT : IsTransversal A' A T) (hS : IsTransversal A'' A' S)
    {φ : G → ℂ} (hφ : ∀ x : G, ∀ d ∈ A', φ (x + d) = φ x) :
    latticeSum A'' A w φ = latticeSum A' A (w * (S.card : ℝ)) φ := by
  classical
  have hφ'' : ∀ x : G, ∀ d ∈ A'', φ (x + d) = φ x := fun x d hd => hφ x d (hle hd)
  rw [latticeSum_eq_sum w (isTransversal_refine hle hle' hT hS) hφ'', latticeSum_eq_sum _ hT hφ,
    Finset.sum_image fun ts hts ts' hts' h => ?_, Finset.sum_product]
  · have hinner : ∀ t ∈ T, ∑ s ∈ S, φ (t + s) = ∑ s ∈ S, φ t :=
      fun t _ => Finset.sum_congr rfl fun s hs => hφ t s (hS.1 s hs)
    dsimp only
    rw [Finset.sum_congr rfl hinner]
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    push_cast
    ring
  · rw [Finset.mem_coe, Finset.mem_product] at hts hts'
    obtain ⟨h₁, h₂⟩ := refine_pairs_eq hle hT hS hts.1 hts.2 hts'.1 hts'.2 (by rw [h, sub_self]; exact A''.zero_mem)
    exact Prod.ext h₁ h₂

private theorem isTransversal_image_mul {F : Type*} [Field F] [DecidableEq F] {A' A : AddSubgroup F} {c : F}
    (hc : c ≠ 0) {T : Finset F} (hT : IsTransversal (dilate c A') (dilate c A) T) :
    IsTransversal A' A (T.image fun t => c * t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    exact mem_dilate.mp (hT.1 t ht)
  · intro a ha
    have ha' : c⁻¹ * a ∈ dilate c A := by
      rw [mem_dilate, mul_inv_cancel_left₀ hc]
      exact ha
    obtain ⟨t, ht, hat⟩ := hT.2.1 _ ha'
    refine ⟨c * t, Finset.mem_image_of_mem _ ht, ?_⟩
    have := mem_dilate.mp hat
    rwa [mul_sub, mul_inv_cancel_left₀ hc] at this
  · intro q hq q' hq' hqq'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hq'
    rw [← mul_sub] at hqq'
    rw [hT.2.2 t ht t' ht' (mem_dilate.mpr hqq')]

private theorem latticeSum_dilate {F : Type*} [Field F] {A' A : AddSubgroup F} {c : F} (hc : c ≠ 0) (w : ℝ)
    {T : Finset F} (hT : IsTransversal (dilate c A') (dilate c A) T) {φ : F → ℂ}
    (hφ : ∀ x : F, ∀ d ∈ A', φ (x + d) = φ x) :
    latticeSum (dilate c A') (dilate c A) w (fun x => φ (c * x)) = latticeSum A' A w φ := by
  classical
  have hφ' : ∀ x : F, ∀ d ∈ dilate c A', φ (c * (x + d)) = φ (c * x) := fun x d hd => by
    rw [mul_add]
    exact hφ _ _ (mem_dilate.mp hd)
  rw [latticeSum_eq_sum (φ := fun x => φ (c * x)) w hT hφ', latticeSum_eq_sum w (isTransversal_image_mul hc hT) hφ,
    Finset.sum_image fun t _ t' _ h => mul_left_cancel₀ hc h]

private theorem isTransversal_filter {G : Type*} [AddCommGroup G] {A' B A : AddSubgroup G} (hA'B : A' ≤ B)
    (hBA : B ≤ A) [DecidablePred fun p : G => p ∈ B] {T : Finset G} (hT : IsTransversal A' A T) :
    IsTransversal A' B (T.filter fun p => p ∈ B) := by
  refine ⟨fun p hp => (Finset.mem_filter.mp hp).2, ?_, ?_⟩
  · intro b hb
    obtain ⟨p, hp, hbp⟩ := hT.2.1 b (hBA hb)
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, hbp⟩
    have := B.sub_mem hb (hA'B hbp)
    rwa [sub_sub_cancel] at this
  · intro p hp p' hp' h
    exact hT.2.2 p (Finset.mem_filter.mp hp).1 p' (Finset.mem_filter.mp hp').1 h

private theorem latticeSum_indicator {G : Type*} [AddCommGroup G] {A' B A : AddSubgroup G} (hA'B : A' ≤ B)
    (hBA : B ≤ A) (w : ℝ) {T S : Finset G} (hT : IsTransversal A' A T) (hS : IsTransversal A' B S) (z : ℂ) :
    latticeSum A' A w (Set.indicator (B : Set G) fun _ => z) = (w : ℂ) * (S.card : ℂ) * z := by
  classical
  have hinv : ∀ x : G, ∀ d ∈ A', Set.indicator (B : Set G) (fun _ => z) (x + d) =
      Set.indicator (B : Set G) (fun _ => z) x := by
    intro x d hd
    have hiff : x + d ∈ (B : Set G) ↔ x ∈ (B : Set G) := by
      simp only [SetLike.mem_coe]
      constructor
      · intro h
        simpa using B.sub_mem h (hA'B hd)
      · intro h
        exact B.add_mem h (hA'B hd)
    simp only [Set.indicator_apply, hiff]
  rw [latticeSum_eq_sum w hT hinv]
  simp only [Set.indicator_apply, SetLike.mem_coe, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  rw [count_eq_of_isTransversal (isTransversal_filter hA'B hBA hT) hS]
  ring

private theorem latticeSum_of_indicator {G : Type*} [AddCommGroup G] {A' B A : AddSubgroup G} (hA'B : A' ≤ B)
    (hBA : B ≤ A) (w : ℝ) {T : Finset G} (hT : IsTransversal A' A T) {φ : G → ℂ}
    (hφ : ∀ x : G, ∀ d ∈ A', φ (x + d) = φ x) :
    latticeSum A' A w (Set.indicator (B : Set G) φ) = latticeSum A' B w φ := by
  classical
  have hinv : ∀ x : G, ∀ d ∈ A', Set.indicator (B : Set G) φ (x + d) = Set.indicator (B : Set G) φ x := by
    intro x d hd
    have hiff : x + d ∈ (B : Set G) ↔ x ∈ (B : Set G) := by
      simp only [SetLike.mem_coe]
      constructor
      · intro h
        simpa using B.sub_mem h (hA'B hd)
      · intro h
        exact B.add_mem h (hA'B hd)
    simp only [Set.indicator_apply, hiff, hφ x d hd]
  rw [latticeSum_eq_sum w hT hinv, latticeSum_eq_sum w (isTransversal_filter hA'B hBA hT) hφ]
  simp only [Set.indicator_apply, SetLike.mem_coe, Finset.sum_ite, Finset.sum_const_zero, add_zero]

end LanglandsTunnell.CubicInduction.LevelLattice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace LevelLattice
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private noncomputable def unif (v : HeightOneSpectrum (𝓞 ℚ)) : v.adicCompletion ℚ :=
  (NumberField.AdelicLevel.uniformizerUnit ℚ v : v.adicCompletion ℚ)

private theorem unif_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) : unif v ≠ 0 := Units.ne_zero _

private theorem norm_unif_pos (v : HeightOneSpectrum (𝓞 ℚ)) : 0 < ‖unif v‖ := norm_pos_iff.mpr (unif_ne_zero v)

private theorem valued_unif_zpow (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℤ) :
    Valued.v (unif v ^ k) = WithZero.exp (-k) := by
  unfold unif
  rw [map_zpow₀, NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zsmul, smul_eq_mul]
  congr 1
  ring

private noncomputable def ballWeight (v : HeightOneSpectrum (𝓞 ℚ)) (b : ℤ) : ℝ := ‖unif v‖ ^ (-b)

private theorem ballWeight_pos (v : HeightOneSpectrum (𝓞 ℚ)) (b : ℤ) : 0 < ballWeight v b :=
  zpow_pos (norm_unif_pos v) _

private theorem ballWeight_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (b : ℤ) : ballWeight v b ≠ 0 :=
  (ballWeight_pos v b).ne'

private theorem ballWeight_div (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℤ) :
    ballWeight v a / ballWeight v b = ‖unif v‖ ^ (b - a) := by
  unfold ballWeight
  rw [← zpow_sub₀ (norm_unif_pos v).ne']
  congr 1
  ring

private theorem exists_ball_transversal (v : HeightOneSpectrum (𝓞 ℚ)) {a b : ℤ} (hba : b ≤ a) :
    ∃ T : Finset (v.adicCompletion ℚ),
      IsTransversal (levelBall (F := v.adicCompletion ℚ) b) (levelBall a) T ∧
        (T.card : ℝ) = ballWeight v a / ballWeight v b := by
  have hc : Valued.v (unif v ^ (a - b)) = WithZero.exp (b - a) := by
    rw [valued_unif_zpow]
    congr 1
    ring
  obtain ⟨hfin, hcount⟩ := finite_and_natCard_dilate_levelBall v b (b - a) (by omega) _ hc
  haveI := hfin
  obtain ⟨T, hT, hTcount⟩ :=
    isTransversal_of_finite (levelBall (F := v.adicCompletion ℚ) b) (dilate (unif v ^ (a - b)) (levelBall b))
  have heq : dilate (unif v ^ (a - b)) (levelBall (F := v.adicCompletion ℚ) b) = levelBall a := by
    rw [dilate_levelBall_eq hc]
    congr 1
    ring
  rw [heq] at hT
  refine ⟨T, hT, ?_⟩
  rw [hTcount, hcount, norm_zpow, ballWeight_div, ← zpow_neg]
  congr 1
  ring

private noncomputable def ballSum (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℤ) (φ : v.adicCompletion ℚ → ℂ) : ℂ :=
  latticeSum (levelBall (F := v.adicCompletion ℚ) b) (levelBall a) (ballWeight v b) φ

private theorem ballSum_add (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℤ) (φ ψ : v.adicCompletion ℚ → ℂ) :
    ballSum v a b (φ + ψ) = ballSum v a b φ + ballSum v a b ψ := by
  unfold ballSum
  exact latticeSum_add _ _ _ _ _

private theorem ballSum_smul (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℤ) (z : ℂ) (φ : v.adicCompletion ℚ → ℂ) :
    ballSum v a b (fun x => z * φ x) = z * ballSum v a b φ := by
  unfold ballSum
  exact latticeSum_smul _ _ _ _ _

private theorem ballSum_congr (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℤ) {φ ψ : v.adicCompletion ℚ → ℂ}
    (h : ∀ x ∈ levelBall (F := v.adicCompletion ℚ) a, φ x = ψ x) : ballSum v a b φ = ballSum v a b ψ := by
  unfold ballSum
  exact latticeSum_congr _ _ _ h

private theorem ballSum_zero (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℤ) :
    ballSum v a b (fun _ => (0 : ℂ)) = 0 := by
  unfold ballSum
  exact latticeSum_zero _ _ _

private theorem ballSum_refine (v : HeightOneSpectrum (𝓞 ℚ)) {a b b' : ℤ} (hb : b' ≤ b) (hba : b ≤ a)
    {φ : v.adicCompletion ℚ → ℂ}
    (hφ : ∀ x : v.adicCompletion ℚ, ∀ d ∈ levelBall (F := v.adicCompletion ℚ) b, φ (x + d) = φ x) :
    ballSum v a b' φ = ballSum v a b φ := by
  obtain ⟨T, hT, -⟩ := exists_ball_transversal v hba
  obtain ⟨S, hS, hScount⟩ := exists_ball_transversal v hb
  have hw : ballWeight v b' * (ballWeight v b / ballWeight v b') = ballWeight v b := by
    have := ballWeight_ne_zero v b'
    field_simp
  unfold ballSum
  rw [latticeSum_refine (levelBall_mono hb) (levelBall_mono hba) _ hT hS hφ, hScount, hw]

private theorem ballSum_translate (v : HeightOneSpectrum (𝓞 ℚ)) {a b : ℤ} (hba : b ≤ a)
    {φ : v.adicCompletion ℚ → ℂ}
    (hφ : ∀ x : v.adicCompletion ℚ, ∀ d ∈ levelBall (F := v.adicCompletion ℚ) b, φ (x + d) = φ x)
    {y : v.adicCompletion ℚ} (hy : y ∈ levelBall (F := v.adicCompletion ℚ) a) :
    ballSum v a b (fun x => φ (x + y)) = ballSum v a b φ := by
  obtain ⟨T, hT, -⟩ := exists_ball_transversal v hba
  unfold ballSum
  exact latticeSum_translate _ hT hφ hy

private theorem ballSum_of_indicator (v : HeightOneSpectrum (𝓞 ℚ)) {a b k : ℤ} (hbk : b ≤ k) (hka : k ≤ a)
    {φ : v.adicCompletion ℚ → ℂ}
    (hφ : ∀ x : v.adicCompletion ℚ, ∀ d ∈ levelBall (F := v.adicCompletion ℚ) b, φ (x + d) = φ x) :
    ballSum v a b (Set.indicator (levelBall (F := v.adicCompletion ℚ) k : Set (v.adicCompletion ℚ)) φ) =
      ballSum v k b φ := by
  obtain ⟨T, hT, -⟩ := exists_ball_transversal v (hbk.trans hka)
  unfold ballSum
  exact latticeSum_of_indicator (levelBall_mono hbk) (levelBall_mono hka) _ hT hφ

private theorem ballSum_indicator_const (v : HeightOneSpectrum (𝓞 ℚ)) {a b k : ℤ} (hbk : b ≤ k) (hka : k ≤ a)
    (z : ℂ) :
    ballSum v a b (Set.indicator (levelBall (F := v.adicCompletion ℚ) k : Set (v.adicCompletion ℚ)) fun _ => z) =
      (ballWeight v k : ℂ) * z := by
  obtain ⟨T, hT, -⟩ := exists_ball_transversal v (hbk.trans hka)
  obtain ⟨S, hS, hScount⟩ := exists_ball_transversal v hbk
  have hw : (ballWeight v b : ℂ) * ((ballWeight v k : ℂ) / (ballWeight v b : ℂ)) = ballWeight v k := by
    have : (ballWeight v b : ℂ) ≠ 0 := by exact_mod_cast ballWeight_ne_zero v b
    field_simp
  have hS' : (S.card : ℂ) = ((ballWeight v k / ballWeight v b : ℝ) : ℂ) := by
    rw [← hScount]
    norm_cast
  unfold ballSum
  rw [latticeSum_indicator (levelBall_mono hbk) (levelBall_mono hka) _ hT hS z, hS']
  push_cast
  rw [hw]

private theorem valued_ne_zero_of_valued_eq_exp (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℤ} {c : v.adicCompletion ℚ}
    (hc : Valued.v c = WithZero.exp n) : c ≠ 0 := by
  intro h
  rw [h, map_zero] at hc
  exact WithZero.exp_ne_zero hc.symm

private theorem norm_eq_of_valued_of_nonpos (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℤ} (hn : n ≤ 0)
    {c : v.adicCompletion ℚ} (hc : Valued.v c = WithZero.exp n) : ‖c‖ = ‖unif v‖ ^ (-n) := by
  obtain ⟨hfin, hcount⟩ := finite_and_natCard_dilate_levelBall v 0 n hn c hc
  haveI := hfin
  obtain ⟨T₀, hT₀, hT₀count⟩ :=
    isTransversal_of_finite (levelBall (F := v.adicCompletion ℚ) 0) (dilate c (levelBall 0))
  rw [dilate_levelBall_eq hc] at hT₀
  obtain ⟨T, hT, hTcount⟩ := exists_ball_transversal v (a := 0 - n) (b := 0) (by omega)
  have hcards : (T₀.card : ℝ) = T.card := by rw [count_eq_of_isTransversal hT₀ hT]
  rw [hT₀count, hcount, hTcount, ballWeight_div] at hcards
  rw [← inv_inv ‖c‖, hcards, ← zpow_neg]
  congr 1
  ring

private theorem norm_eq_of_valued (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℤ} {c : v.adicCompletion ℚ}
    (hc : Valued.v c = WithZero.exp n) : ‖c‖ = ‖unif v‖ ^ (-n) := by
  rcases le_or_gt n 0 with hn | hn
  · exact norm_eq_of_valued_of_nonpos v hn hc
  · have hc' : Valued.v c⁻¹ = WithZero.exp (-n) := by
      rw [map_inv₀, hc, ← WithZero.exp_neg]
    have h := norm_eq_of_valued_of_nonpos v (by omega) hc'
    rw [norm_inv, neg_neg] at h
    rw [← inv_inv ‖c‖, h, ← zpow_neg]

private theorem ballSum_dilate (v : HeightOneSpectrum (𝓞 ℚ)) {a b n : ℤ} {c : v.adicCompletion ℚ}
    (hc : Valued.v c = WithZero.exp n) (hba : b ≤ a) {φ : v.adicCompletion ℚ → ℂ}
    (hφ : ∀ x : v.adicCompletion ℚ, ∀ d ∈ levelBall (F := v.adicCompletion ℚ) b, φ (x + d) = φ x) :
    ballSum v (a - n) (b - n) (fun x => φ (c * x)) = ((‖c‖⁻¹ : ℝ) : ℂ) * ballSum v a b φ := by
  have hc0 : c ≠ 0 := valued_ne_zero_of_valued_eq_exp v hc
  obtain ⟨T, hT, -⟩ := exists_ball_transversal v (a := a - n) (b := b - n) (by omega)
  rw [← dilate_levelBall_eq (m := b) hc, ← dilate_levelBall_eq (m := a) hc] at hT
  have hw : ballWeight v (b - n) = ‖c‖⁻¹ * ballWeight v b := by
    unfold ballWeight
    rw [norm_eq_of_valued v hc, ← zpow_neg, neg_neg, ← zpow_add₀ (norm_unif_pos v).ne']
    congr 1
    ring
  unfold ballSum
  rw [← latticeSum_dilate hc0 (ballWeight v b) hT hφ, dilate_levelBall_eq hc, dilate_levelBall_eq hc, hw,
    latticeSum_weight]

private theorem ballSum_dilate_unit (v : HeightOneSpectrum (𝓞 ℚ)) {a b : ℤ} {c : v.adicCompletion ℚ}
    (hc : Valued.v c = 1) (hba : b ≤ a) {φ : v.adicCompletion ℚ → ℂ}
    (hφ : ∀ x : v.adicCompletion ℚ, ∀ d ∈ levelBall (F := v.adicCompletion ℚ) b, φ (x + d) = φ x) :
    ballSum v a b (fun x => φ (c * x)) = ballSum v a b φ := by
  have hc' : Valued.v c = WithZero.exp (0 : ℤ) := by rw [hc, WithZero.exp_zero]
  have h := ballSum_dilate v hc' hba hφ
  rw [sub_zero, sub_zero, norm_eq_of_valued v hc', neg_zero, zpow_zero, inv_one] at h
  simpa using h

end LanglandsTunnell.CubicInduction.LevelLattice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace LevelLattice
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private theorem norm_unif_lt_one (v : HeightOneSpectrum (𝓞 ℚ)) : ‖unif v‖ < 1 := by
  obtain ⟨T, hT, hTcount⟩ := exists_ball_transversal v (a := 1) (b := 0) (by norm_num)
  have hπ : unif v ^ (-1 : ℤ) ∈ levelBall (F := v.adicCompletion ℚ) 1 :=
    mem_levelBall.mpr (le_of_eq (by rw [valued_unif_zpow, neg_neg]))
  have hπ0 : unif v ^ (-1 : ℤ) ∉ levelBall (F := v.adicCompletion ℚ) 0 := by
    rw [mem_levelBall, valued_unif_zpow, neg_neg, WithZero.exp_le_exp]
    norm_num
  obtain ⟨p, hp, hp0⟩ := hT.2.1 0 (levelBall (F := v.adicCompletion ℚ) 1).zero_mem
  obtain ⟨q, hq, hqπ⟩ := hT.2.1 _ hπ
  have hpq : p ≠ q := by
    rintro rfl
    apply hπ0
    have h := (levelBall (F := v.adicCompletion ℚ) 0).sub_mem hqπ hp0
    rwa [sub_sub_sub_cancel_right, sub_zero] at h
  have h2 : (2 : ℝ) ≤ T.card := by
    have : 1 < T.card := Finset.one_lt_card.mpr ⟨p, hp, q, hq, hpq⟩
    exact_mod_cast this
  rw [hTcount, ballWeight_div] at h2
  have hpos := norm_unif_pos v
  have h3 := mul_le_mul_of_nonneg_left h2 hpos.le
  rw [show (0 : ℤ) - 1 = -1 by norm_num, zpow_neg_one, mul_inv_cancel₀ hpos.ne'] at h3
  linarith

private theorem eventually_mem_levelBall (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℤ) :
    ∀ᶠ y in nhds (0 : v.adicCompletion ℚ), y ∈ levelBall (F := v.adicCompletion ℚ) m := by
  have h := eventually_valued_lt v (zpow_ne_zero (-m) (unif_ne_zero v))
  rw [valued_unif_zpow, neg_neg] at h
  exact h.mono fun y hy => (mem_levelBall.mpr hy.le)

private theorem eventually_sub_mem_levelBall (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) (m : ℤ) :
    ∀ᶠ y in nhds x, y - x ∈ levelBall (F := v.adicCompletion ℚ) m := by
  have ht : Filter.Tendsto (fun y : v.adicCompletion ℚ => y - x) (nhds x) (nhds (x - x)) :=
    (continuous_id.sub continuous_const).tendsto x
  rw [sub_self] at ht
  exact ht.eventually (eventually_mem_levelBall v m)

private theorem norm_le_of_valued_le (v : HeightOneSpectrum (𝓞 ℚ)) {k : ℤ} {z : v.adicCompletion ℚ}
    (hz : Valued.v z ≤ WithZero.exp k) : ‖z‖ ≤ ‖unif v‖ ^ (-k) := by
  by_cases h0 : z = 0
  · rw [h0, norm_zero]
    exact (zpow_pos (norm_unif_pos v) _).le
  · have hv : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
    have hz' : Valued.v z = WithZero.exp (WithZero.log (Valued.v z)) := (WithZero.exp_log hv).symm
    have hk : WithZero.log (Valued.v z) ≤ k := by
      rw [hz', WithZero.exp_le_exp] at hz
      exact hz
    rw [norm_eq_of_valued v hz']
    exact zpow_le_zpow_right_of_le_one₀ (norm_unif_pos v) (norm_unif_lt_one v).le (neg_le_neg hk)

private theorem exists_levelBall_of_eventually (v : HeightOneSpectrum (𝓞 ℚ)) {x : v.adicCompletion ℚ}
    {p : v.adicCompletion ℚ → Prop} (hp : ∀ᶠ y in nhds x, p y) :
    ∃ m : ℤ, ∀ y : v.adicCompletion ℚ, y - x ∈ levelBall (F := v.adicCompletion ℚ) m → p y := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hp
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (norm_unif_lt_one v)
  refine ⟨-n, fun y hy => hball ?_⟩
  rw [dist_eq_norm]
  have h := norm_le_of_valued_le v (mem_levelBall.mp hy)
  rw [neg_neg, zpow_natCast] at h
  exact lt_of_le_of_lt h hn

private theorem isCompact_levelBall (v : HeightOneSpectrum (𝓞 ℚ)) (R : ℤ) :
    IsCompact (levelBall (F := v.adicCompletion ℚ) R : Set (v.adicCompletion ℚ)) := by
  have hc : CompactSpace (v.adicCompletionIntegers ℚ) := inferInstance
  have hO : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := isCompact_iff_compactSpace.mpr hc
  have himage : (levelBall (F := v.adicCompletion ℚ) R : Set (v.adicCompletion ℚ)) =
      (fun x => unif v ^ (-R) * x) '' (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
    ext y
    constructor
    · intro hy
      refine ⟨unif v ^ R * y, ?_, ?_⟩
      · show unif v ^ R * y ∈ v.adicCompletionIntegers ℚ
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, valued_unif_zpow]
        calc WithZero.exp (-R) * Valued.v y ≤ WithZero.exp (-R) * WithZero.exp R :=
              mul_le_mul_right (mem_levelBall.mp hy) _
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
      · show unif v ^ (-R) * (unif v ^ R * y) = y
        rw [zpow_neg, inv_mul_cancel_left₀ (zpow_ne_zero R (unif_ne_zero v))]
    · rintro ⟨x, hx, rfl⟩
      have hx' : Valued.v x ≤ 1 := by
        rwa [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hx
      show Valued.v (unif v ^ (-R) * x) ≤ WithZero.exp R
      rw [Valuation.map_mul, valued_unif_zpow, neg_neg]
      exact mul_le_of_le_one_right' hx'
  rw [himage]
  exact hO.image (continuous_const.mul continuous_id)

private theorem exists_lower_bound_on_finset {ι : Type*} (t : Finset ι) (lv : ι → ℤ) :
    ∃ m : ℤ, ∀ i ∈ t, m ≤ lv i := by
  rcases t.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp⟩
  · obtain ⟨i₀, -, hi₀⟩ := t.exists_min_image lv hne
    exact ⟨lv i₀, hi₀⟩

private theorem exists_uniform_level (v : HeightOneSpectrum (𝓞 ℚ)) {ψ : v.adicCompletion ℚ → ℂ}
    (hψ : IsLocallyConstant ψ) (R : ℤ) :
    ∃ m : ℤ, ∀ x ∈ levelBall (F := v.adicCompletion ℚ) R, ∀ d ∈ levelBall (F := v.adicCompletion ℚ) m,
      ψ (x + d) = ψ x := by
  have hpt : ∀ x : v.adicCompletion ℚ, ∃ m : ℤ,
      ∀ y : v.adicCompletion ℚ, y - x ∈ levelBall (F := v.adicCompletion ℚ) m → ψ y = ψ x :=
    fun x => exists_levelBall_of_eventually v (hψ.eventually_eq x)
  choose lv hlv using hpt
  obtain ⟨t, -, hcover⟩ := (isCompact_levelBall v R).elim_nhds_subcover
    (fun x => {y | y - x ∈ levelBall (F := v.adicCompletion ℚ) (lv x)})
    (fun x _ => eventually_sub_mem_levelBall v x (lv x))
  obtain ⟨m, hm⟩ := exists_lower_bound_on_finset t lv
  refine ⟨m, fun x hx d hd => ?_⟩
  obtain ⟨x₀, hx₀t, hxx₀⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hxx₀' : x - x₀ ∈ levelBall (F := v.adicCompletion ℚ) (lv x₀) := hxx₀
  have hd' : d ∈ levelBall (F := v.adicCompletion ℚ) (lv x₀) := levelBall_mono (hm x₀ hx₀t) hd
  have hxd : x + d - x₀ ∈ levelBall (F := v.adicCompletion ℚ) (lv x₀) := by
    rw [add_sub_right_comm]
    exact (levelBall (F := v.adicCompletion ℚ) (lv x₀)).add_mem hxx₀' hd'
  rw [hlv x₀ (x + d) hxd, hlv x₀ x hxx₀']

end LanglandsTunnell.CubicInduction.LevelLattice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace LevelLattice
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private noncomputable def linePt (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : LocalGL2 v :=
  antidiagonal2 v * upperUnipotent2 v x

private theorem linePt_coe (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    (linePt v x : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, x] := by
  unfold linePt
  rw [Units.val_mul, antidiagonal2_coe, upperUnipotent2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private noncomputable def lineFn (v : HeightOneSpectrum (𝓞 ℚ)) (f : LocalGL2 v → ℂ) (x : v.adicCompletion ℚ) : ℂ :=
  f (linePt v x)

private theorem lineFn_add (v : HeightOneSpectrum (𝓞 ℚ)) (f f' : LocalGL2 v → ℂ) :
    lineFn v (f + f') = lineFn v f + lineFn v f' :=
  rfl

private theorem lineFn_smul (v : HeightOneSpectrum (𝓞 ℚ)) (z : ℂ) (f : LocalGL2 v → ℂ) :
    lineFn v (z • f) = fun x => z * lineFn v f x :=
  rfl

private theorem lineFn_rightTranslate_upperUnipotent (v : HeightOneSpectrum (𝓞 ℚ)) (f : LocalGL2 v → ℂ)
    (y x : v.adicCompletion ℚ) :
    lineFn v (rightTranslate2 v (upperUnipotent2 v y) f) x = lineFn v f (x + y) := by
  unfold lineFn linePt
  rw [rightTranslate2_apply, mul_assoc, upperUnipotent2_mul]

private theorem linePt_mul_diagonal2_coe (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ)
    (d : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    ((linePt v x * diagonal2 v d : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      !![0, (d 1 : v.adicCompletion ℚ); (d 0 : v.adicCompletion ℚ), x * (d 1 : v.adicCompletion ℚ)] := by
  rw [Units.val_mul, linePt_coe, diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagonal2_swap_mul_linePt_coe (v : HeightOneSpectrum (𝓞 ℚ)) (y : v.adicCompletion ℚ)
    (d : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    ((diagonal2 v ![d 1, d 0] * linePt v y : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      !![0, (d 1 : v.adicCompletion ℚ); (d 0 : v.adicCompletion ℚ), (d 0 : v.adicCompletion ℚ) * y] := by
  rw [Units.val_mul, linePt_coe, diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem linePt_mul_diagonal2 (v : HeightOneSpectrum (𝓞 ℚ)) {x y : v.adicCompletion ℚ}
    (d : Fin 2 → (v.adicCompletion ℚ)ˣ) (hy : (d 0 : v.adicCompletion ℚ) * y = x * d 1) :
    linePt v x * diagonal2 v d = diagonal2 v ![d 1, d 0] * linePt v y := by
  apply Units.ext
  rw [linePt_mul_diagonal2_coe, diagonal2_swap_mul_linePt_coe, hy]

private theorem lineFn_rightTranslate_diagonal2 (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v χ)
    (d : Fin 2 → (v.adicCompletion ℚ)ˣ) {x y : v.adicCompletion ℚ} (hy : (d 0 : v.adicCompletion ℚ) * y = x * d 1) :
    lineFn v (rightTranslate2 v (diagonal2 v d) f) x =
      torusChar2 v χ ![d 1, d 0] * halfModulus2 v ![d 1, d 0] * lineFn v f y := by
  obtain ⟨-, -, hT⟩ := mem_principalSeries2_iff.mp hf
  unfold lineFn
  rw [rightTranslate2_apply, linePt_mul_diagonal2 v d hy, hT]

private theorem linePt_mul_antidiagonal2_coe (v : HeightOneSpectrum (𝓞 ℚ)) (u : v.adicCompletion ℚ) :
    ((linePt v u * antidiagonal2 v : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, 0; u, 1] := by
  rw [Units.val_mul, linePt_coe, antidiagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagonal2_mul_lower_coe (v : HeightOneSpectrum (𝓞 ℚ)) (u : v.adicCompletion ℚ)
    (α β : (v.adicCompletion ℚ)ˣ) :
    ((diagonal2 v ![α, β] * (linePt v u * antidiagonal2 v) : LocalGL2 v) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      !![(α : v.adicCompletion ℚ), 0; (β : v.adicCompletion ℚ) * u, (β : v.adicCompletion ℚ)] := by
  rw [Units.val_mul, diagonal2_coe, linePt_mul_antidiagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem bruhat_coe (v : HeightOneSpectrum (𝓞 ℚ)) (u : v.adicCompletion ℚ) (α β : (v.adicCompletion ℚ)ˣ) :
    ((upperUnipotent2 v u * (diagonal2 v ![α, β] * (linePt v u * antidiagonal2 v)) : LocalGL2 v) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      !![(α : v.adicCompletion ℚ) + u * (β : v.adicCompletion ℚ) * u, u * (β : v.adicCompletion ℚ);
        (β : v.adicCompletion ℚ) * u, (β : v.adicCompletion ℚ)] := by
  rw [Units.val_mul, upperUnipotent2_coe, diagonal2_mul_lower_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem linePt_eq_bruhat (v : HeightOneSpectrum (𝓞 ℚ)) {x u : v.adicCompletion ℚ}
    {α β : (v.adicCompletion ℚ)ˣ} (hβ : (β : v.adicCompletion ℚ) = x) (hu : u * (β : v.adicCompletion ℚ) = 1)
    (hu' : (β : v.adicCompletion ℚ) * u = 1) (hα : (α : v.adicCompletion ℚ) + u * (β : v.adicCompletion ℚ) * u = 0) :
    linePt v x = upperUnipotent2 v u * (diagonal2 v ![α, β] * (linePt v u * antidiagonal2 v)) := by
  apply Units.ext
  rw [linePt_coe, bruhat_coe, hα, hu, hu', hβ]

private theorem lineFn_eq_of_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v χ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    lineFn v f x =
      torusChar2 v χ ![Units.mk0 (-x⁻¹) (neg_ne_zero.mpr (inv_ne_zero hx)), Units.mk0 x hx] *
        halfModulus2 v ![Units.mk0 (-x⁻¹) (neg_ne_zero.mpr (inv_ne_zero hx)), Units.mk0 x hx] *
          lineFn v (rightTranslate2 v (antidiagonal2 v) f) x⁻¹ := by
  obtain ⟨-, hN, hT⟩ := mem_principalSeries2_iff.mp hf
  have hid := linePt_eq_bruhat v (x := x) (u := x⁻¹) (α := Units.mk0 (-x⁻¹) (neg_ne_zero.mpr (inv_ne_zero hx)))
    (β := Units.mk0 x hx) rfl (by simp [hx]) (by simp [hx]) (by simp [hx])
  unfold lineFn
  rw [hid, hN, hT, rightTranslate2_apply]

private theorem continuous_matrix_of_entries (v : HeightOneSpectrum (𝓞 ℚ)) (p q r : v.adicCompletion ℚ)
    {φ : v.adicCompletion ℚ → v.adicCompletion ℚ} (hφ : Continuous φ) :
    Continuous fun x : v.adicCompletion ℚ => (!![p, q; r, φ x] : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first | exact continuous_const | exact hφ

private theorem continuous_matrix_of_entries' (v : HeightOneSpectrum (𝓞 ℚ)) (p r s : v.adicCompletion ℚ)
    {φ : v.adicCompletion ℚ → v.adicCompletion ℚ} (hφ : Continuous φ) :
    Continuous fun x : v.adicCompletion ℚ => (!![p, φ x; r, s] : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first | exact continuous_const | exact hφ

private theorem upperUnipotent2_inv_val (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    (((upperUnipotent2 v x)⁻¹ : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, -x; 0, 1] :=
  rfl

private theorem linePt_inv_val (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    (((linePt v x)⁻¹ : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      !![1, -x; 0, 1] * (((antidiagonal2 v)⁻¹ : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  unfold linePt
  rw [_root_.mul_inv_rev, Units.val_mul, upperUnipotent2_inv_val]

private theorem continuous_linePt (v : HeightOneSpectrum (𝓞 ℚ)) : Continuous (linePt v) := by
  rw [Units.isInducing_embedProduct.continuous_iff]
  have hval : Continuous fun x : v.adicCompletion ℚ =>
      (!![0, 1; 1, x] : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
    continuous_matrix_of_entries v 0 1 1 continuous_id
  have hinv : Continuous fun x : v.adicCompletion ℚ =>
      (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
        (((antidiagonal2 v)⁻¹ : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
    (continuous_matrix_of_entries' v 1 0 1 continuous_neg).mul continuous_const
  refine (hval.prodMk (MulOpposite.continuous_op.comp hinv)).congr fun x => ?_
  simp only [Function.comp_apply, Units.embedProduct_apply, linePt_coe, linePt_inv_val]

private theorem isLocallyConstant_lineFn (v : HeightOneSpectrum (𝓞 ℚ)) {f : LocalGL2 v → ℂ}
    (hf : IsLocallyConstant f) : IsLocallyConstant (lineFn v f) :=
  hf.comp_continuous (continuous_linePt v)

private theorem cornerEntry2_linePt (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    cornerEntry2 v (linePt v x) = 1 := by
  unfold cornerEntry2 gl2Entry
  rw [linePt_coe]
  simp

private theorem gl2Entry_linePt_one_one (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    gl2Entry v (linePt v x) 1 1 = x := by
  unfold gl2Entry
  rw [linePt_coe]
  simp

private theorem gl2Det_linePt (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : gl2Det v (linePt v x) = -1 := by
  unfold gl2Det
  rw [linePt_coe, Matrix.det_fin_two_of]
  ring

private theorem linePt_mem_cellCutoff2_iff (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    linePt v x ∈ cellCutoff2 v ↔ x ∈ levelBall (F := v.adicCompletion ℚ) 0 := by
  simp only [cellCutoff2, Set.mem_setOf_eq, cornerEntry2_linePt, gl2Entry_linePt_one_one, ne_eq, one_ne_zero,
    not_false_eq_true, true_and, div_one, mem_levelBall, WithZero.exp_zero]

private theorem charExt_apply_one (v : HeightOneSpectrum (𝓞 ℚ)) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) :
    TateLocal.charExt χ (1 : v.adicCompletion ℚ) = 1 := by
  simpa using TateLocal.charExt_coe_units χ (1 : (v.adicCompletion ℚ)ˣ)

private theorem lineFn_cellSection2 (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    lineFn v (cellSection2 v χ) =
      Set.indicator (levelBall (F := v.adicCompletion ℚ) 0 : Set (v.adicCompletion ℚ))
        fun _ => TateLocal.charExt (χ 0) (-1 : v.adicCompletion ℚ) := by
  funext x
  unfold lineFn cellSection2
  by_cases hx : x ∈ levelBall (F := v.adicCompletion ℚ) 0
  · rw [Set.indicator_of_mem ((linePt_mem_cellCutoff2_iff v x).mpr hx), Set.indicator_of_mem (by exact hx)]
    simp only [cellValue2, gl2Det_linePt, cornerEntry2_linePt, div_one, charExt_apply_one, norm_neg, norm_one,
      Real.sqrt_one, Complex.ofReal_one, mul_one]
  · rw [Set.indicator_of_notMem (fun h => hx ((linePt_mem_cellCutoff2_iff v x).mp h)),
      Set.indicator_of_notMem (by exact hx)]

private theorem cellSection2_one (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    cellSection2 v χ 1 = 0 := by
  unfold cellSection2
  apply Set.indicator_of_notMem
  rintro ⟨h1, -⟩
  apply h1
  unfold cornerEntry2 gl2Entry
  rw [Units.val_one]
  exact Matrix.one_apply_ne (by decide)

end LanglandsTunnell.CubicInduction.LevelLattice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace LevelLattice
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private noncomputable def IsSchwartz (v : HeightOneSpectrum (𝓞 ℚ)) (R b : ℤ) (ψ : v.adicCompletion ℚ → ℂ) : Prop :=
  b ≤ R ∧ (∀ x : v.adicCompletion ℚ, ∀ d ∈ levelBall (F := v.adicCompletion ℚ) b, ψ (x + d) = ψ x) ∧
    ∀ x : v.adicCompletion ℚ, x ∉ levelBall (F := v.adicCompletion ℚ) R → ψ x = 0

private theorem IsSchwartz.mono (v : HeightOneSpectrum (𝓞 ℚ)) {R b R' b' : ℤ} {ψ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b ψ) (hR : R ≤ R') (hb : b' ≤ b) : IsSchwartz v R' b' ψ := by
  obtain ⟨hbR, hinv, hsupp⟩ := h
  refine ⟨(hb.trans hbR).trans hR, fun x d hd => hinv x d (levelBall_mono hb hd), fun x hx => hsupp x ?_⟩
  exact fun hxR => hx (levelBall_mono hR hxR)

private theorem exists_mem_levelBall (v : HeightOneSpectrum (𝓞 ℚ)) (y : v.adicCompletion ℚ) :
    ∃ k : ℤ, y ∈ levelBall (F := v.adicCompletion ℚ) k := by
  by_cases hy : y = 0
  · refine ⟨0, ?_⟩
    rw [hy]
    exact (levelBall (F := v.adicCompletion ℚ) 0).zero_mem
  · have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    exact ⟨WithZero.log (Valued.v y), mem_levelBall.mpr (WithZero.exp_log hv).symm.le⟩

private theorem exists_isSchwartz (v : HeightOneSpectrum (𝓞 ℚ)) {ψ : v.adicCompletion ℚ → ℂ} (hψ : IsLocallyConstant ψ)
    {R : ℤ} (hR : ∀ x : v.adicCompletion ℚ, x ∉ levelBall (F := v.adicCompletion ℚ) R → ψ x = 0) :
    ∃ b : ℤ, IsSchwartz v R b ψ := by
  obtain ⟨m, hm⟩ := exists_uniform_level v hψ R
  refine ⟨min m R, min_le_right _ _, fun x d hd => ?_, hR⟩
  have hdm : d ∈ levelBall (F := v.adicCompletion ℚ) m := levelBall_mono (min_le_left _ _) hd
  have hdR : d ∈ levelBall (F := v.adicCompletion ℚ) R := levelBall_mono (min_le_right _ _) hd
  by_cases hx : x ∈ levelBall (F := v.adicCompletion ℚ) R
  · exact hm x hx d hdm
  · have hxd : x + d ∉ levelBall (F := v.adicCompletion ℚ) R := fun h => by
      apply hx
      have := (levelBall (F := v.adicCompletion ℚ) R).sub_mem h hdR
      rwa [add_sub_cancel_right] at this
    rw [hR x hx, hR (x + d) hxd]

private noncomputable def csInt (v : HeightOneSpectrum (𝓞 ℚ)) (ψ : v.adicCompletion ℚ → ℂ) : ℂ := by
  classical
  exact if h : ∃ p : ℤ × ℤ, IsSchwartz v p.1 p.2 ψ then ballSum v h.choose.1 h.choose.2 ψ else 0

private theorem ballSum_of_isSchwartz_le (v : HeightOneSpectrum (𝓞 ℚ)) {R b R' : ℤ} {ψ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b ψ) (hR : R ≤ R') : ballSum v R' b ψ = ballSum v R b ψ := by
  obtain ⟨hbR, hinv, hsupp⟩ := h
  have hψ : ψ = Set.indicator (levelBall (F := v.adicCompletion ℚ) R : Set (v.adicCompletion ℚ)) ψ := by
    funext x
    by_cases hx : x ∈ levelBall (F := v.adicCompletion ℚ) R
    · rw [Set.indicator_of_mem (by exact hx)]
    · rw [Set.indicator_of_notMem (by exact hx), hsupp x hx]
  conv_lhs => rw [hψ]
  exact ballSum_of_indicator v hbR hR hinv

private theorem ballSum_eq_of_isSchwartz (v : HeightOneSpectrum (𝓞 ℚ)) {R b R' b' : ℤ}
    {ψ : v.adicCompletion ℚ → ℂ} (h : IsSchwartz v R b ψ) (h' : IsSchwartz v R' b' ψ) :
    ballSum v R b ψ = ballSum v R' b' ψ := by
  have e1 : ballSum v R b ψ = ballSum v (max R R') (min b b') ψ := by
    rw [ballSum_of_isSchwartz_le v (IsSchwartz.mono v h le_rfl (min_le_left _ _)) (le_max_left _ _)]
    exact (ballSum_refine v (min_le_left b b') h.1 h.2.1).symm
  have e2 : ballSum v R' b' ψ = ballSum v (max R R') (min b b') ψ := by
    rw [ballSum_of_isSchwartz_le v (IsSchwartz.mono v h' le_rfl (min_le_right _ _)) (le_max_right _ _)]
    exact (ballSum_refine v (min_le_right b b') h'.1 h'.2.1).symm
  rw [e1, e2]

private theorem csInt_eq (v : HeightOneSpectrum (𝓞 ℚ)) {R b : ℤ} {ψ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b ψ) :
    csInt v ψ = ballSum v R b ψ := by
  unfold csInt
  have hex : ∃ p : ℤ × ℤ, IsSchwartz v p.1 p.2 ψ := ⟨(R, b), h⟩
  rw [dif_pos hex]
  exact ballSum_eq_of_isSchwartz v hex.choose_spec h

private theorem IsSchwartz.add (v : HeightOneSpectrum (𝓞 ℚ)) {R b R' b' : ℤ} {φ ψ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b φ) (h' : IsSchwartz v R' b' ψ) : IsSchwartz v (max R R') (min b b') (φ + ψ) := by
  obtain ⟨-, hinv, hsupp⟩ := IsSchwartz.mono v h (le_max_left R R') (min_le_left b b')
  obtain ⟨hbR, hinv', hsupp'⟩ := IsSchwartz.mono v h' (le_max_right R R') (min_le_right b b')
  refine ⟨hbR, fun x d hd => ?_, fun x hx => ?_⟩
  · simp only [Pi.add_apply, hinv x d hd, hinv' x d hd]
  · simp only [Pi.add_apply, hsupp x hx, hsupp' x hx, add_zero]

private theorem IsSchwartz.smul (v : HeightOneSpectrum (𝓞 ℚ)) {R b : ℤ} {φ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b φ) (z : ℂ) : IsSchwartz v R b fun x => z * φ x := by
  obtain ⟨hbR, hinv, hsupp⟩ := h
  exact ⟨hbR, fun x d hd => by simp only [hinv x d hd], fun x hx => by simp only [hsupp x hx, mul_zero]⟩

private theorem IsSchwartz.translate (v : HeightOneSpectrum (𝓞 ℚ)) {R b : ℤ} {φ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b φ) {y : v.adicCompletion ℚ} {k : ℤ} (hy : y ∈ levelBall (F := v.adicCompletion ℚ) k) :
    IsSchwartz v (max R k) (min b k) fun x => φ (x + y) := by
  obtain ⟨hbR, hinv, hsupp⟩ := IsSchwartz.mono v h (le_max_left R k) (min_le_left b k)
  refine ⟨hbR, fun x d hd => ?_, fun x hx => ?_⟩
  · show φ (x + d + y) = φ (x + y)
    rw [add_right_comm]
    exact hinv (x + y) d hd
  · show φ (x + y) = 0
    refine hsupp (x + y) fun hxy => hx ?_
    have := (levelBall (F := v.adicCompletion ℚ) (max R k)).sub_mem hxy (levelBall_mono (le_max_right R k) hy)
    rwa [add_sub_cancel_right] at this

private theorem IsSchwartz.dilate (v : HeightOneSpectrum (𝓞 ℚ)) {R b n : ℤ} {φ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b φ) {c : v.adicCompletion ℚ} (hc : Valued.v c = WithZero.exp n) :
    IsSchwartz v (R - n) (b - n) fun x => φ (c * x) := by
  obtain ⟨hbR, hinv, hsupp⟩ := h
  refine ⟨by omega, fun x d hd => ?_, fun x hx => ?_⟩
  · show φ (c * (x + d)) = φ (c * x)
    rw [mul_add]
    refine hinv (c * x) (c * d) ?_
    rw [← mem_dilate, dilate_levelBall_eq hc]
    exact hd
  · show φ (c * x) = 0
    refine hsupp (c * x) fun hcx => hx ?_
    rw [← dilate_levelBall_eq hc, mem_dilate]
    exact hcx

private theorem isSchwartz_indicator_const (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℤ) (z : ℂ) :
    IsSchwartz v k k
      (Set.indicator (levelBall (F := v.adicCompletion ℚ) k : Set (v.adicCompletion ℚ)) fun _ => z) := by
  refine ⟨le_rfl, fun x d hd => ?_, fun x hx => Set.indicator_of_notMem (by exact hx) _⟩
  by_cases hx : x ∈ levelBall (F := v.adicCompletion ℚ) k
  · rw [Set.indicator_of_mem (by exact (levelBall (F := v.adicCompletion ℚ) k).add_mem hx hd),
      Set.indicator_of_mem (by exact hx)]
  · have hxd : x + d ∉ levelBall (F := v.adicCompletion ℚ) k := fun h => by
      apply hx
      have := (levelBall (F := v.adicCompletion ℚ) k).sub_mem h hd
      rwa [add_sub_cancel_right] at this
    rw [Set.indicator_of_notMem (by exact hxd), Set.indicator_of_notMem (by exact hx)]

private theorem csInt_add (v : HeightOneSpectrum (𝓞 ℚ)) {R b R' b' : ℤ} {φ ψ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b φ) (h' : IsSchwartz v R' b' ψ) : csInt v (φ + ψ) = csInt v φ + csInt v ψ := by
  rw [csInt_eq v (IsSchwartz.add v h h'), csInt_eq v (IsSchwartz.mono v h (le_max_left R R') (min_le_left b b')),
    csInt_eq v (IsSchwartz.mono v h' (le_max_right R R') (min_le_right b b')), ballSum_add]

private theorem csInt_smul (v : HeightOneSpectrum (𝓞 ℚ)) {R b : ℤ} {φ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b φ) (z : ℂ) : csInt v (fun x => z * φ x) = z * csInt v φ := by
  rw [csInt_eq v (IsSchwartz.smul v h z), csInt_eq v h, ballSum_smul]

private theorem csInt_sub (v : HeightOneSpectrum (𝓞 ℚ)) {R b R' b' : ℤ} {φ ψ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b φ) (h' : IsSchwartz v R' b' ψ) : csInt v (φ - ψ) = csInt v φ - csInt v ψ := by
  have hψ : φ - ψ = φ + fun x => (-1 : ℂ) * ψ x := by
    funext x
    simp [sub_eq_add_neg]
  rw [hψ, csInt_add v h (IsSchwartz.smul v h' (-1)), csInt_smul v h', neg_one_mul, sub_eq_add_neg]

private theorem csInt_translate (v : HeightOneSpectrum (𝓞 ℚ)) {R b : ℤ} {φ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b φ) (y : v.adicCompletion ℚ) : csInt v (fun x => φ (x + y)) = csInt v φ := by
  obtain ⟨k, hk⟩ := exists_mem_levelBall v y
  have hm : IsSchwartz v (max R k) (min b k) φ := IsSchwartz.mono v h (le_max_left R k) (min_le_left b k)
  rw [csInt_eq v (IsSchwartz.translate v h hk), csInt_eq v hm]
  exact ballSum_translate v hm.1 hm.2.1 (levelBall_mono (le_max_right R k) hk)

private theorem csInt_dilate (v : HeightOneSpectrum (𝓞 ℚ)) {R b n : ℤ} {φ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b φ) {c : v.adicCompletion ℚ} (hc : Valued.v c = WithZero.exp n) :
    csInt v (fun x => φ (c * x)) = ((‖c‖⁻¹ : ℝ) : ℂ) * csInt v φ := by
  rw [csInt_eq v (IsSchwartz.dilate v h hc), csInt_eq v h]
  exact ballSum_dilate v hc h.1 h.2.1

private theorem csInt_indicator_const (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℤ) (z : ℂ) :
    csInt v (Set.indicator (levelBall (F := v.adicCompletion ℚ) k : Set (v.adicCompletion ℚ)) fun _ => z) =
      (ballWeight v k : ℂ) * z := by
  rw [csInt_eq v (isSchwartz_indicator_const v k z)]
  exact ballSum_indicator_const v le_rfl le_rfl z

end LanglandsTunnell.CubicInduction.LevelLattice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace LevelLattice
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private noncomputable def ratioChar (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) :
    (v.adicCompletion ℚ)ˣ →* ℂˣ :=
  b * a⁻¹

private theorem ratioChar_apply (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (u : (v.adicCompletion ℚ)ˣ) : ((ratioChar v a b u : ℂˣ) : ℂ) = (b u : ℂ) * ((a u : ℂˣ) : ℂ)⁻¹ := by
  simp [ratioChar]

private theorem ratioChar_ne_one (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ} (hab : a ≠ b) :
    ratioChar v a b ≠ 1 := by
  intro h
  unfold ratioChar at h
  exact hab (mul_inv_eq_one.mp h).symm

private theorem charExt_ratioChar (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (x : v.adicCompletion ℚ) :
    TateLocal.charExt (ratioChar v a b) x = TateLocal.charExt b x * (TateLocal.charExt a x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [TateLocal.charExt_of_ne_zero _ hx, TateLocal.charExt_of_ne_zero _ hx, TateLocal.charExt_of_ne_zero _ hx,
      ratioChar_apply]

private noncomputable def cutModel (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) (m : ℤ)
    (x : v.adicCompletion ℚ) : ℂ := by
  classical
  exact if x ∈ levelBall (F := v.adicCompletion ℚ) m then 0
    else TateLocal.charExt (ratioChar v a b) x * ((‖x‖⁻¹ : ℝ) : ℂ)

private theorem cutModel_of_mem (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) {m : ℤ}
    {x : v.adicCompletion ℚ} (hx : x ∈ levelBall (F := v.adicCompletion ℚ) m) : cutModel v a b m x = 0 := by
  unfold cutModel
  rw [if_pos hx]

private theorem cutModel_of_notMem (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) {m : ℤ}
    {x : v.adicCompletion ℚ} (hx : x ∉ levelBall (F := v.adicCompletion ℚ) m) :
    cutModel v a b m x = TateLocal.charExt (ratioChar v a b) x * ((‖x‖⁻¹ : ℝ) : ℂ) := by
  unfold cutModel
  rw [if_neg hx]

private theorem cutModel_sub_apply_of_notMem (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    {m m' : ℤ} {x : v.adicCompletion ℚ} (hx : x ∉ levelBall (F := v.adicCompletion ℚ) (max m m')) :
    (cutModel v a b m - cutModel v a b m') x = 0 := by
  have hm : x ∉ levelBall (F := v.adicCompletion ℚ) m := fun h => hx (levelBall_mono (le_max_left m m') h)
  have hm' : x ∉ levelBall (F := v.adicCompletion ℚ) m' := fun h => hx (levelBall_mono (le_max_right m m') h)
  rw [Pi.sub_apply, cutModel_of_notMem v a b hm, cutModel_of_notMem v a b hm', sub_self]

private theorem isLocallyConstant_cutModel (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) (m : ℤ) : IsLocallyConstant (cutModel v a b m) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ levelBall (F := v.adicCompletion ℚ) m
  · filter_upwards [eventually_sub_mem_levelBall v x m] with y hy
    have hy' : y ∈ levelBall (F := v.adicCompletion ℚ) m := by
      have := (levelBall (F := v.adicCompletion ℚ) m).add_mem hy hx
      rwa [sub_add_cancel] at this
    rw [cutModel_of_mem v a b hy', cutModel_of_mem v a b hx]
  · have hx0 : x ≠ 0 := fun h => hx (by rw [h]; exact (levelBall (F := v.adicCompletion ℚ) m).zero_mem)
    filter_upwards [eventually_sub_mem_levelBall v x m, eventually_charExt_eq v a hla hx0,
      eventually_charExt_eq v b hlb hx0, eventually_norm_eq v hx0] with y hy hya hyb hyn
    have hy' : y ∉ levelBall (F := v.adicCompletion ℚ) m := fun hym => by
      apply hx
      have := (levelBall (F := v.adicCompletion ℚ) m).sub_mem hym hy
      rwa [sub_sub_cancel] at this
    rw [cutModel_of_notMem v a b hy', cutModel_of_notMem v a b hx, charExt_ratioChar, charExt_ratioChar, hya, hyb, hyn]

private theorem cutModel_unit_mul (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) (m : ℤ)
    {u : (v.adicCompletion ℚ)ˣ} (hu : Valued.v (u : v.adicCompletion ℚ) = 1) (x : v.adicCompletion ℚ) :
    cutModel v a b m ((u : v.adicCompletion ℚ) * x) = ((ratioChar v a b u : ℂˣ) : ℂ) * cutModel v a b m x := by
  have hmem : (u : v.adicCompletion ℚ) * x ∈ levelBall (F := v.adicCompletion ℚ) m ↔
      x ∈ levelBall (F := v.adicCompletion ℚ) m := by
    rw [mem_levelBall, mem_levelBall, Valuation.map_mul, hu, one_mul]
  have hnorm : ‖(u : v.adicCompletion ℚ)‖ = 1 := by
    have h := norm_eq_of_valued v (n := 0) (c := (u : v.adicCompletion ℚ)) (by rw [hu, WithZero.exp_zero])
    rwa [neg_zero, zpow_zero] at h
  by_cases hx : x ∈ levelBall (F := v.adicCompletion ℚ) m
  · rw [cutModel_of_mem v a b (hmem.mpr hx), cutModel_of_mem v a b hx, mul_zero]
  · rw [cutModel_of_notMem v a b (fun h => hx (hmem.mp h)), cutModel_of_notMem v a b hx, charExt_units_mul, norm_mul,
      hnorm, one_mul, mul_assoc]

private theorem cutModel_zero_mul_eq (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) {n : ℤ}
    {c : (v.adicCompletion ℚ)ˣ} (hc : Valued.v (c : v.adicCompletion ℚ) = WithZero.exp n) (x : v.adicCompletion ℚ) :
    ((ratioChar v a b c : ℂˣ) : ℂ)⁻¹ * ((‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) *
        cutModel v a b 0 ((c : v.adicCompletion ℚ) * x) =
      cutModel v a b (-n) x := by
  have hmem : (c : v.adicCompletion ℚ) * x ∈ levelBall (F := v.adicCompletion ℚ) 0 ↔
      x ∈ levelBall (F := v.adicCompletion ℚ) (-n) := by
    rw [← mem_dilate, dilate_levelBall_eq hc, zero_sub]
  by_cases hx : x ∈ levelBall (F := v.adicCompletion ℚ) (-n)
  · rw [cutModel_of_mem v a b (hmem.mpr hx), cutModel_of_mem v a b hx, mul_zero]
  · have hη : ((ratioChar v a b c : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hcn : ((‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr c.ne_zero)
    rw [cutModel_of_notMem v a b (fun h => hx (hmem.mp h)), cutModel_of_notMem v a b hx, charExt_units_mul, norm_mul,
      mul_inv]
    push_cast
    linear_combination
      (((‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) * ((‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ)⁻¹ *
          TateLocal.charExt (ratioChar v a b) x * ((‖x‖ : ℝ) : ℂ)⁻¹) * inv_mul_cancel₀ hη +
        (TateLocal.charExt (ratioChar v a b) x * ((‖x‖ : ℝ) : ℂ)⁻¹) * mul_inv_cancel₀ hcn

private theorem IsSchwartz.sub (v : HeightOneSpectrum (𝓞 ℚ)) {R b R' b' : ℤ} {φ ψ : v.adicCompletion ℚ → ℂ}
    (h : IsSchwartz v R b φ) (h' : IsSchwartz v R' b' ψ) : IsSchwartz v (max R R') (min b b') (φ - ψ) := by
  have e : φ - ψ = φ + fun x => (-1 : ℂ) * ψ x := by
    funext x
    simp [sub_eq_add_neg]
  rw [e]
  exact IsSchwartz.add v h (IsSchwartz.smul v h' (-1))

private theorem csInt_zero (v : HeightOneSpectrum (𝓞 ℚ)) : csInt v (0 : v.adicCompletion ℚ → ℂ) = 0 := by
  have h : IsSchwartz v 0 0 (0 : v.adicCompletion ℚ → ℂ) := ⟨le_rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩
  rw [csInt_eq v h]
  exact ballSum_zero v 0 0

private theorem exists_isSchwartz_cutModel_sub (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) (m m' : ℤ) :
    ∃ k : ℤ, IsSchwartz v (max m m') k (cutModel v a b m - cutModel v a b m') :=
  exists_isSchwartz v ((isLocallyConstant_cutModel v hla hlb m).sub (isLocallyConstant_cutModel v hla hlb m'))
    fun _ hx => cutModel_sub_apply_of_notMem v a b hx

private theorem csInt_eq_zero_of_covariant (v : HeightOneSpectrum (𝓞 ℚ)) {R k : ℤ} {D : v.adicCompletion ℚ → ℂ}
    (hD : IsSchwartz v R k D) {u : (v.adicCompletion ℚ)ˣ} (hu : Valued.v (u : v.adicCompletion ℚ) = 1) {z : ℂ}
    (hz : z ≠ 1) (hcov : ∀ x : v.adicCompletion ℚ, D ((u : v.adicCompletion ℚ) * x) = z * D x) : csInt v D = 0 := by
  have hnorm : ‖(u : v.adicCompletion ℚ)‖ = 1 := by
    have h := norm_eq_of_valued v (n := 0) (c := (u : v.adicCompletion ℚ)) (by rw [hu, WithZero.exp_zero])
    rwa [neg_zero, zpow_zero] at h
  have h1 : csInt v (fun x => D ((u : v.adicCompletion ℚ) * x)) = csInt v D := by
    rw [csInt_dilate v hD (n := 0) (c := (u : v.adicCompletion ℚ)) (by rw [hu, WithZero.exp_zero]), hnorm]
    simp
  have h2 : csInt v (fun x => D ((u : v.adicCompletion ℚ) * x)) = z * csInt v D := by
    rw [show (fun x => D ((u : v.adicCompletion ℚ) * x)) = fun x => z * D x from funext hcov, csInt_smul v hD]
  have h3 : (z - 1) * csInt v D = 0 := by
    rw [sub_mul, one_mul, ← h2, h1, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hz)

end LanglandsTunnell.CubicInduction.LevelLattice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace LevelLattice
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private noncomputable def unifUnit (v : HeightOneSpectrum (𝓞 ℚ)) : (v.adicCompletion ℚ)ˣ :=
  NumberField.AdelicLevel.uniformizerUnit ℚ v

private theorem coe_unifUnit (v : HeightOneSpectrum (𝓞 ℚ)) : (unifUnit v : v.adicCompletion ℚ) = unif v := rfl

private theorem valued_unifUnit_zpow (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℤ) :
    Valued.v ((unifUnit v ^ k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, coe_unifUnit, valued_unif_zpow]

private noncomputable def geomBase (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) : ℂ :=
  ((ratioChar v a b (unifUnit v) : ℂˣ) : ℂ)⁻¹

private theorem geomBase_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) :
    geomBase v a b ≠ 0 :=
  inv_ne_zero (Units.ne_zero _)

private theorem exists_valued_eq_exp (v : HeightOneSpectrum (𝓞 ℚ)) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    ∃ j : ℤ, Valued.v x = WithZero.exp j :=
  ⟨WithZero.log (Valued.v x), (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx)).symm⟩

private theorem charExt_ratioChar_eq_zpow (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hU : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ratioChar v a b u = 1)
    {x : v.adicCompletion ℚ} {k : ℤ} (hx : Valued.v x = WithZero.exp k) :
    TateLocal.charExt (ratioChar v a b) x = geomBase v a b ^ k := by
  have hx0 : x ≠ 0 := valued_ne_zero_of_valued_eq_exp v hx
  have hw : Valued.v ((unifUnit v ^ k * Units.mk0 x hx0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_mul, Valuation.map_mul, valued_unifUnit_zpow, Units.val_mk0, hx, ← WithZero.exp_add, neg_add_cancel,
      WithZero.exp_zero]
  have h1 := hU _ hw
  rw [map_mul, map_zpow] at h1
  rw [TateLocal.charExt_of_ne_zero _ hx0, eq_inv_of_mul_eq_one_right h1, geomBase, Units.val_inv_eq_inv_val,
    Units.val_zpow_eq_zpow_val, _root_.inv_zpow]

private theorem geomBase_ne_one (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ} (hab : a ≠ b)
    (hU : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ratioChar v a b u = 1) :
    geomBase v a b ≠ 1 := by
  intro ht
  apply ratioChar_ne_one v hab
  refine MonoidHom.ext fun u => Units.ext ?_
  rw [MonoidHom.one_apply, Units.val_one]
  obtain ⟨k, hk⟩ := exists_valued_eq_exp v u.ne_zero
  have h := charExt_ratioChar_eq_zpow v a b hU hk
  rw [TateLocal.charExt_coe_units, ht, _root_.one_zpow] at h
  exact h

private theorem valued_eq_of_mem_shell (v : HeightOneSpectrum (𝓞 ℚ)) {k : ℤ} {x : v.adicCompletion ℚ}
    (hx : x ∈ levelBall (F := v.adicCompletion ℚ) (k + 1)) (hx' : x ∉ levelBall (F := v.adicCompletion ℚ) k) :
    Valued.v x = WithZero.exp (k + 1) := by
  have hx0 : x ≠ 0 := fun h => hx' (by rw [h]; exact (levelBall (F := v.adicCompletion ℚ) k).zero_mem)
  obtain ⟨j, hj⟩ := exists_valued_eq_exp v hx0
  rw [mem_levelBall, hj, WithZero.exp_le_exp] at hx hx'
  rw [hj]
  congr 1
  omega

private theorem cutModel_sub_succ (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hU : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ratioChar v a b u = 1) (k : ℤ) :
    cutModel v a b k - cutModel v a b (k + 1) = fun x =>
      geomBase v a b ^ (k + 1) * ((‖unif v‖ ^ (k + 1) : ℝ) : ℂ) *
        ((Set.indicator (levelBall (F := v.adicCompletion ℚ) (k + 1) : Set (v.adicCompletion ℚ)) fun _ => (1 : ℂ)) -
          Set.indicator (levelBall (F := v.adicCompletion ℚ) k : Set (v.adicCompletion ℚ)) fun _ => (1 : ℂ)) x := by
  funext x
  rw [Pi.sub_apply, Pi.sub_apply]
  by_cases hk : x ∈ levelBall (F := v.adicCompletion ℚ) k
  · have hk1 : x ∈ levelBall (F := v.adicCompletion ℚ) (k + 1) := levelBall_mono (by omega) hk
    rw [cutModel_of_mem v a b hk, cutModel_of_mem v a b hk1, Set.indicator_of_mem (by exact hk1),
      Set.indicator_of_mem (by exact hk), sub_self, sub_self, mul_zero]
  · by_cases hk1 : x ∈ levelBall (F := v.adicCompletion ℚ) (k + 1)
    · have hv := valued_eq_of_mem_shell v hk1 hk
      rw [cutModel_of_notMem v a b hk, cutModel_of_mem v a b hk1, sub_zero, charExt_ratioChar_eq_zpow v a b hU hv,
        norm_eq_of_valued v hv, Set.indicator_of_mem (by exact hk1), Set.indicator_of_notMem (by exact hk), sub_zero,
        mul_one, _root_.zpow_neg, inv_inv]
    · rw [cutModel_of_notMem v a b hk, cutModel_of_notMem v a b hk1, sub_self, Set.indicator_of_notMem (by exact hk1),
        Set.indicator_of_notMem (by exact hk), sub_zero, mul_zero]

private theorem csInt_shell (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hU : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ratioChar v a b u = 1) (k : ℤ) :
    csInt v (cutModel v a b k - cutModel v a b (k + 1)) = geomBase v a b ^ (k + 1) * (1 - ((‖unif v‖ : ℝ) : ℂ)) := by
  rw [cutModel_sub_succ v a b hU k]
  have h1 := isSchwartz_indicator_const v (k + 1) (1 : ℂ)
  have h0 := isSchwartz_indicator_const v k (1 : ℂ)
  rw [csInt_smul v (IsSchwartz.sub v h1 h0), csInt_sub v h1 h0, csInt_indicator_const, csInt_indicator_const, mul_one,
    mul_one]
  unfold ballWeight
  have hu0 : ‖unif v‖ ≠ 0 := (norm_unif_pos v).ne'
  have hk0 : ‖unif v‖ ^ k ≠ 0 := zpow_ne_zero k hu0
  have hreal : ‖unif v‖ ^ (k + 1) * (‖unif v‖ ^ (-(k + 1)) - ‖unif v‖ ^ (-k)) = 1 - ‖unif v‖ := by
    rw [_root_.zpow_neg, _root_.zpow_neg, zpow_add_one₀ hu0, mul_sub, mul_inv_cancel₀ (mul_ne_zero hk0 hu0)]
    congr 1
    rw [mul_comm (‖unif v‖ ^ k) ‖unif v‖, mul_inv_cancel_right₀ hk0]
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
  push_cast at hc ⊢
  linear_combination geomBase v a b ^ (k + 1) * hc

private noncomputable def geomConst (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) : ℂ :=
  (1 - ((‖unif v‖ : ℝ) : ℂ)) * geomBase v a b / (1 - geomBase v a b)

private theorem csInt_cutModel_sub_zero (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) (hab : a ≠ b)
    (hU : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ratioChar v a b u = 1) (m : ℤ) :
    csInt v (cutModel v a b m - cutModel v a b 0) = (geomBase v a b ^ m - 1) * geomConst v a b := by
  have ht1 : 1 - geomBase v a b ≠ 0 := sub_ne_zero.mpr (geomBase_ne_one v hab hU).symm
  have ht0 := geomBase_ne_zero v a b
  refine Int.induction_on m ?_ (fun i ih => ?_) (fun i ih => ?_)
  · rw [sub_self, csInt_zero, zpow_zero, sub_self, zero_mul]
  · have e : cutModel v a b ((i : ℤ) + 1) - cutModel v a b 0 =
        (cutModel v a b i - cutModel v a b 0) - (cutModel v a b i - cutModel v a b ((i : ℤ) + 1)) := by
      abel
    obtain ⟨k₁, h₁⟩ := exists_isSchwartz_cutModel_sub v hla hlb i 0
    obtain ⟨k₂, h₂⟩ := exists_isSchwartz_cutModel_sub v hla hlb i ((i : ℤ) + 1)
    rw [e, csInt_sub v h₁ h₂, ih, csInt_shell v a b hU i, zpow_add_one₀ ht0]
    unfold geomConst
    field_simp
    ring
  · have e : cutModel v a b (-(i : ℤ) - 1) - cutModel v a b 0 =
        (cutModel v a b (-(i : ℤ)) - cutModel v a b 0) +
          (cutModel v a b (-(i : ℤ) - 1) - cutModel v a b (-(i : ℤ))) := by
      abel
    obtain ⟨k₁, h₁⟩ := exists_isSchwartz_cutModel_sub v hla hlb (-(i : ℤ)) 0
    obtain ⟨k₂, h₂⟩ := exists_isSchwartz_cutModel_sub v hla hlb (-(i : ℤ) - 1) (-(i : ℤ))
    have hs := csInt_shell v a b hU (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by omega] at hs
    have hsplit : geomBase v a b ^ (-(i : ℤ)) = geomBase v a b ^ (-(i : ℤ) - 1) * geomBase v a b := by
      rw [← zpow_add_one₀ ht0]
      congr 1
      omega
    rw [e, csInt_add v h₁ h₂, ih, hs, hsplit]
    unfold geomConst
    field_simp
    ring

private theorem csInt_cutModel_sub_zero_of_ramified (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) {u : (v.adicCompletion ℚ)ˣ}
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) (hηu : ratioChar v a b u ≠ 1) (m : ℤ) :
    csInt v (cutModel v a b m - cutModel v a b 0) = 0 := by
  obtain ⟨k, hk⟩ := exists_isSchwartz_cutModel_sub v hla hlb m 0
  refine csInt_eq_zero_of_covariant v hk hu (z := ((ratioChar v a b u : ℂˣ) : ℂ))
    (fun h => hηu (Units.val_eq_one.mp h)) fun x => ?_
  rw [Pi.sub_apply, Pi.sub_apply, cutModel_unit_mul v a b m hu x, cutModel_unit_mul v a b 0 hu x, mul_sub]

private theorem exists_model_constant (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) (hab : a ≠ b) :
    ∃ e : ℂ, ∀ (c : (v.adicCompletion ℚ)ˣ) (n : ℤ), Valued.v (c : v.adicCompletion ℚ) = WithZero.exp n →
      csInt v (cutModel v a b (-n) - cutModel v a b 0) = (((ratioChar v a b c : ℂˣ) : ℂ)⁻¹ - 1) * e := by
  by_cases hU : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → ratioChar v a b u = 1
  · refine ⟨geomConst v a b, fun c n hc => ?_⟩
    have h := charExt_ratioChar_eq_zpow v a b hU hc
    rw [TateLocal.charExt_coe_units] at h
    rw [h, ← _root_.zpow_neg, csInt_cutModel_sub_zero v hla hlb hab hU (-n)]
  · obtain ⟨u, hu⟩ := not_forall.mp hU
    have huv : Valued.v (u : v.adicCompletion ℚ) = 1 := by
      by_contra h
      exact hu fun h' => absurd h' h
    have hηu : ratioChar v a b u ≠ 1 := fun h => hu fun _ => h
    exact ⟨0, fun c n _ => by rw [csInt_cutModel_sub_zero_of_ramified v hla hlb huv hηu, mul_zero]⟩

private theorem sqrt_div_swap {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Real.sqrt (p / q) = Real.sqrt (q / p) * (p * q⁻¹) := by
  have hs : Real.sqrt (q / p) ≠ 0 := (Real.sqrt_pos.mpr (div_pos hq hp)).ne'
  have h2 : Real.sqrt (q / p) * Real.sqrt (q / p) = q / p := Real.mul_self_sqrt (div_pos hq hp).le
  rw [← inv_div, Real.sqrt_inv]
  calc (Real.sqrt (q / p))⁻¹ = (Real.sqrt (q / p) * Real.sqrt (q / p))⁻¹ * Real.sqrt (q / p) := by
        rw [mul_inv, inv_mul_cancel_right₀ hs]
    _ = Real.sqrt (q / p) * (p * q⁻¹) := by
        rw [h2, inv_div, div_eq_mul_inv, mul_comm (p * q⁻¹) (Real.sqrt (q / p))]

private theorem ratioChar_pair (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (d : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    ((ratioChar v a b (d 1 * (d 0)⁻¹) : ℂˣ) : ℂ) =
      (b (d 1) : ℂ) * ((a (d 1) : ℂˣ) : ℂ)⁻¹ * (((b (d 0) : ℂˣ) : ℂ) * ((a (d 0) : ℂˣ) : ℂ)⁻¹)⁻¹ := by
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, ratioChar_apply, ratioChar_apply]

private theorem torus_const_swap (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (d : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    torusChar2 v ![a, b] ![d 1, d 0] * halfModulus2 v ![d 1, d 0] =
      torusChar2 v ![a, b] d * halfModulus2 v d *
        (((ratioChar v a b (d 1 * (d 0)⁻¹) : ℂˣ) : ℂ)⁻¹ *
          ((‖((d 1 * (d 0)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ : ℝ) : ℂ)) := by
  have hn0 : 0 < ‖(d 0 : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr (d 0).ne_zero
  have hn1 : 0 < ‖(d 1 : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr (d 1).ne_zero
  have ha0 : ((a (d 0) : ℂˣ) : ℂ) * ((a (d 0) : ℂˣ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero _)
  have hb1 : ((b (d 1) : ℂˣ) : ℂ) * ((b (d 1) : ℂˣ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero _)
  rw [ratioChar_pair, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]
  simp only [torusChar2, halfModulus2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [sqrt_div_swap hn1 hn0]
  push_cast
  simp only [mul_inv, inv_inv]
  linear_combination
    (-(((a (d 1) : ℂˣ) : ℂ) * ((b (d 0) : ℂˣ) : ℂ) *
            ((Real.sqrt (‖(d 0 : v.adicCompletion ℚ)‖ / ‖(d 1 : v.adicCompletion ℚ)‖) : ℝ) : ℂ) *
          ((‖(d 1 : v.adicCompletion ℚ)‖ : ℝ) : ℂ) * ((‖(d 0 : v.adicCompletion ℚ)‖ : ℝ) : ℂ)⁻¹) *
        (((b (d 1) : ℂˣ) : ℂ) * ((b (d 1) : ℂˣ) : ℂ)⁻¹)) * ha0 +
      (-(((a (d 1) : ℂˣ) : ℂ) * ((b (d 0) : ℂˣ) : ℂ) *
            ((Real.sqrt (‖(d 0 : v.adicCompletion ℚ)‖ / ‖(d 1 : v.adicCompletion ℚ)‖) : ℝ) : ℂ) *
          ((‖(d 1 : v.adicCompletion ℚ)‖ : ℝ) : ℂ) * ((‖(d 0 : v.adicCompletion ℚ)‖ : ℝ) : ℂ)⁻¹)) * hb1

private theorem torus_const_ratio (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (d : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    torusChar2 v ![b, a] d * halfModulus2 v d =
      torusChar2 v ![a, b] d * halfModulus2 v d * ((ratioChar v a b (d 1 * (d 0)⁻¹) : ℂˣ) : ℂ)⁻¹ := by
  have ha0 : ((a (d 0) : ℂˣ) : ℂ) * ((a (d 0) : ℂˣ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero _)
  have hb1 : ((b (d 1) : ℂˣ) : ℂ) * ((b (d 1) : ℂˣ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero _)
  rw [ratioChar_pair]
  simp only [torusChar2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_inv, inv_inv]
  linear_combination
    (-(((b (d 0) : ℂˣ) : ℂ) * ((a (d 1) : ℂˣ) : ℂ) * halfModulus2 v d) *
          (((b (d 1) : ℂˣ) : ℂ) * ((b (d 1) : ℂˣ) : ℂ)⁻¹)) * ha0 +
      (-(((b (d 0) : ℂˣ) : ℂ) * ((a (d 1) : ℂˣ) : ℂ) * halfModulus2 v d)) * hb1

private theorem sqrt_inv_div_self {r : ℝ} (hr : 0 < r) : Real.sqrt (r⁻¹ / r) = r⁻¹ := by
  rw [div_eq_mul_inv, Real.sqrt_mul_self (inv_nonneg.mpr hr.le)]

private theorem tail_const (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) {x : v.adicCompletion ℚ}
    (hx : x ≠ 0) (hx0 : x ∉ levelBall (F := v.adicCompletion ℚ) 0) :
    torusChar2 v ![a, b] ![Units.mk0 (-x⁻¹) (neg_ne_zero.mpr (inv_ne_zero hx)), Units.mk0 x hx] *
        halfModulus2 v ![Units.mk0 (-x⁻¹) (neg_ne_zero.mpr (inv_ne_zero hx)), Units.mk0 x hx] =
      ((a (-1) : ℂˣ) : ℂ) * cutModel v a b 0 x := by
  have hneg : Units.mk0 (-x⁻¹) (neg_ne_zero.mpr (inv_ne_zero hx)) = -1 * (Units.mk0 x hx)⁻¹ := by
    ext
    simp
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [cutModel_of_notMem v a b hx0, TateLocal.charExt_of_ne_zero _ hx, ratioChar_apply]
  simp only [torusChar2, halfModulus2, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mk0]
  rw [hneg, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, norm_neg, norm_inv, sqrt_inv_div_self hnx]
  push_cast
  ring

end LanglandsTunnell.CubicInduction.LevelLattice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace LevelLattice
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private theorem antidiagonal2_mul_self (v : HeightOneSpectrum (𝓞 ℚ)) : antidiagonal2 v * antidiagonal2 v = 1 := by
  apply Units.ext
  rw [Units.val_mul, antidiagonal2_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem lineFn_rightTranslate_antidiagonal2_zero (v : HeightOneSpectrum (𝓞 ℚ)) (f : LocalGL2 v → ℂ) :
    lineFn v (rightTranslate2 v (antidiagonal2 v) f) 0 = f 1 := by
  unfold lineFn linePt
  rw [rightTranslate2_apply, upperUnipotent2_zero, mul_one, antidiagonal2_mul_self]

private noncomputable def constTerm (v : HeightOneSpectrum (𝓞 ℚ)) (a : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (f : LocalGL2 v → ℂ) : ℂ :=
  ((a (-1) : ℂˣ) : ℂ) * f 1

private theorem constTerm_add (v : HeightOneSpectrum (𝓞 ℚ)) (a : (v.adicCompletion ℚ)ˣ →* ℂˣ) (f f' : LocalGL2 v → ℂ) :
    constTerm v a (f + f') = constTerm v a f + constTerm v a f' := by
  unfold constTerm
  rw [Pi.add_apply, mul_add]

private theorem constTerm_smul (v : HeightOneSpectrum (𝓞 ℚ)) (a : (v.adicCompletion ℚ)ˣ →* ℂˣ) (z : ℂ)
    (f : LocalGL2 v → ℂ) : constTerm v a (z • f) = z * constTerm v a f := by
  unfold constTerm
  rw [Pi.smul_apply, smul_eq_mul]
  ring

private theorem constTerm_rightTranslate_upperUnipotent (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : (v.adicCompletion ℚ)ˣ →* ℂˣ) {f : LocalGL2 v → ℂ}
    (hf : f ∈ principalSeries2 v χ) (y : v.adicCompletion ℚ) :
    constTerm v a (rightTranslate2 v (upperUnipotent2 v y) f) = constTerm v a f := by
  unfold constTerm
  rw [rightTranslate2_apply, one_mul, ← mul_one (upperUnipotent2 v y), (mem_principalSeries2_iff.mp hf).2.1 y 1]

private theorem constTerm_rightTranslate_diagonal2 (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : (v.adicCompletion ℚ)ˣ →* ℂˣ) {f : LocalGL2 v → ℂ}
    (hf : f ∈ principalSeries2 v χ) (d : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    constTerm v a (rightTranslate2 v (diagonal2 v d) f) = torusChar2 v χ d * halfModulus2 v d * constTerm v a f := by
  unfold constTerm
  rw [rightTranslate2_apply, one_mul, ← mul_one (diagonal2 v d), (mem_principalSeries2_iff.mp hf).2.2 d 1]
  ring

private noncomputable def tailFn (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (f : LocalGL2 v → ℂ) : v.adicCompletion ℚ → ℂ :=
  lineFn v f - fun x => constTerm v a f * cutModel v a b 0 x

private theorem tailFn_apply (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) (f : LocalGL2 v → ℂ)
    (x : v.adicCompletion ℚ) : tailFn v a b f x = lineFn v f x - constTerm v a f * cutModel v a b 0 x :=
  rfl

private theorem inv_mem_levelBall_of_notMem (v : HeightOneSpectrum (𝓞 ℚ)) {k : ℤ} {x : v.adicCompletion ℚ}
    (hx : x ∉ levelBall (F := v.adicCompletion ℚ) (max 0 (-k - 1))) :
    x⁻¹ ∈ levelBall (F := v.adicCompletion ℚ) k := by
  have hx0 : x ≠ 0 := fun h => hx (by rw [h]; exact (levelBall (F := v.adicCompletion ℚ) _).zero_mem)
  obtain ⟨j, hj⟩ := exists_valued_eq_exp v hx0
  rw [mem_levelBall, hj, WithZero.exp_le_exp] at hx
  rw [mem_levelBall, map_inv₀, hj, ← WithZero.exp_neg, WithZero.exp_le_exp]
  omega

private theorem exists_tailFn_eq_zero (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v ![a, b]) :
    ∃ R : ℤ, ∀ x : v.adicCompletion ℚ, x ∉ levelBall (F := v.adicCompletion ℚ) R → tailFn v a b f x = 0 := by
  have hw := rightTranslate2_mem_principalSeries2 hf (antidiagonal2 v)
  obtain ⟨k, hk⟩ := exists_levelBall_of_eventually v
    ((isLocallyConstant_lineFn v (mem_principalSeries2_iff.mp hw).1).eventually_eq 0)
  refine ⟨max 0 (-k - 1), fun x hx => ?_⟩
  have hx0 : x ∉ levelBall (F := v.adicCompletion ℚ) 0 := fun h => hx (levelBall_mono (le_max_left _ _) h)
  have hxne : x ≠ 0 := fun h => hx0 (by rw [h]; exact (levelBall (F := v.adicCompletion ℚ) 0).zero_mem)
  have hinv := hk x⁻¹ (by rw [sub_zero]; exact inv_mem_levelBall_of_notMem v hx)
  rw [tailFn_apply, lineFn_eq_of_ne_zero v ![a, b] hf hxne, tail_const v a b hxne hx0, hinv,
    lineFn_rightTranslate_antidiagonal2_zero]
  unfold constTerm
  ring

private theorem isLocallyConstant_tailFn (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) {f : LocalGL2 v → ℂ} (hf : IsLocallyConstant f) :
    IsLocallyConstant (tailFn v a b f) := by
  unfold tailFn
  exact (isLocallyConstant_lineFn v hf).sub
    ((isLocallyConstant_cutModel v hla hlb 0).comp fun z => constTerm v a f * z)

private theorem exists_isSchwartz_tailFn (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) {f : LocalGL2 v → ℂ}
    (hf : f ∈ principalSeries2 v ![a, b]) :
    ∃ R k : ℤ, IsSchwartz v R k (tailFn v a b f) := by
  obtain ⟨R, hR⟩ := exists_tailFn_eq_zero v a b hf
  obtain ⟨k, hk⟩ := exists_isSchwartz v (isLocallyConstant_tailFn v hla hlb (mem_principalSeries2_iff.mp hf).1) hR
  exact ⟨R, k, hk⟩

private noncomputable def regFn (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) (e : ℂ)
    (f : LocalGL2 v → ℂ) : ℂ :=
  csInt v (tailFn v a b f) + constTerm v a f * e

private theorem tailFn_add (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) (f f' : LocalGL2 v → ℂ) :
    tailFn v a b (f + f') = tailFn v a b f + tailFn v a b f' := by
  funext x
  simp only [tailFn_apply, Pi.add_apply, lineFn_add, constTerm_add]
  ring

private theorem tailFn_smul (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) (z : ℂ)
    (f : LocalGL2 v → ℂ) : tailFn v a b (z • f) = fun x => z * tailFn v a b f x := by
  funext x
  simp only [tailFn_apply, lineFn_smul, constTerm_smul]
  ring

private theorem regFn_add (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ} (hla : IsLocallyConstant a)
    (hlb : IsLocallyConstant b) (e : ℂ) {f f' : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v ![a, b])
    (hf' : f' ∈ principalSeries2 v ![a, b]) : regFn v a b e (f + f') = regFn v a b e f + regFn v a b e f' := by
  obtain ⟨R, k, h⟩ := exists_isSchwartz_tailFn v hla hlb hf
  obtain ⟨R', k', h'⟩ := exists_isSchwartz_tailFn v hla hlb hf'
  unfold regFn
  rw [tailFn_add, csInt_add v h h', constTerm_add]
  ring

private theorem regFn_smul (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) (e : ℂ) {f : LocalGL2 v → ℂ}
    (hf : f ∈ principalSeries2 v ![a, b]) (z : ℂ) :
    regFn v a b e (z • f) = z * regFn v a b e f := by
  obtain ⟨R, k, h⟩ := exists_isSchwartz_tailFn v hla hlb hf
  unfold regFn
  rw [tailFn_smul, csInt_smul v h, constTerm_smul]
  ring

private theorem exists_charExt_ratioChar_one_add_eq_one (v : HeightOneSpectrum (𝓞 ℚ))
    {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ} (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) :
    ∃ N : ℤ, ∀ d ∈ levelBall (F := v.adicCompletion ℚ) N, TateLocal.charExt (ratioChar v a b) (1 + d) = 1 := by
  have h : ∀ᶠ y in nhds (1 : v.adicCompletion ℚ), TateLocal.charExt (ratioChar v a b) y = 1 := by
    filter_upwards [eventually_charExt_eq v a hla one_ne_zero, eventually_charExt_eq v b hlb one_ne_zero] with y ha hb
    rw [charExt_ratioChar, ha, hb, charExt_apply_one, charExt_apply_one, inv_one, mul_one]
  obtain ⟨N, hN⟩ := exists_levelBall_of_eventually v h
  exact ⟨N, fun d hd => hN (1 + d) (by simpa using hd)⟩

private theorem exists_cutModel_add_eq (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) (y : v.adicCompletion ℚ) :
    ∃ m : ℤ, ∀ x : v.adicCompletion ℚ, cutModel v a b m (x + y) = cutModel v a b m x := by
  obtain ⟨N, hN⟩ := exists_charExt_ratioChar_one_add_eq_one v hla hlb
  obtain ⟨l, hl⟩ := exists_mem_levelBall v y
  refine ⟨max l (l - N), fun x => ?_⟩
  by_cases hx : x ∈ levelBall (F := v.adicCompletion ℚ) (max l (l - N))
  · have hxy : x + y ∈ levelBall (F := v.adicCompletion ℚ) (max l (l - N)) :=
      (levelBall (F := v.adicCompletion ℚ) (max l (l - N))).add_mem hx (levelBall_mono (le_max_left _ _) hl)
    rw [cutModel_of_mem v a b hx, cutModel_of_mem v a b hxy]
  · have hx0 : x ≠ 0 := fun h => hx (by rw [h]; exact (levelBall (F := v.adicCompletion ℚ) _).zero_mem)
    obtain ⟨j, hj⟩ := exists_valued_eq_exp v hx0
    rw [mem_levelBall, hj, WithZero.exp_le_exp] at hx
    rw [mem_levelBall] at hl
    have hd : Valued.v (x⁻¹ * y) ≤ WithZero.exp (l - j) := by
      rw [map_mul, map_inv₀, hj, ← WithZero.exp_neg, sub_eq_neg_add, WithZero.exp_add]
      exact mul_le_mul_right hl _
    have hd1 : Valued.v (x⁻¹ * y) < 1 := hd.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    have hu1 : Valued.v (1 + x⁻¹ * y) = 1 := Valued.v.map_one_add_of_lt hd1
    have hv0 : Valued.v (1 + x⁻¹ * y) ≠ 0 := by
      rw [hu1]
      exact one_ne_zero
    have hune : (1 + x⁻¹ * y) ≠ 0 := (Valuation.ne_zero_iff _).mp hv0
    have hunit : Valued.v ((Units.mk0 (1 + x⁻¹ * y) hune : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
      rw [Units.val_mk0, hu1]
    have hη : ((ratioChar v a b (Units.mk0 (1 + x⁻¹ * y) hune) : ℂˣ) : ℂ) = 1 := by
      rw [← TateLocal.charExt_coe_units, Units.val_mk0]
      exact hN _ (by rw [mem_levelBall]; exact hd.trans (WithZero.exp_le_exp.mpr (by omega)))
    have hxy : x + y = (Units.mk0 (1 + x⁻¹ * y) hune : v.adicCompletion ℚ) * x := by
      rw [Units.val_mk0, add_mul, one_mul, mul_comm x⁻¹ y, inv_mul_cancel_right₀ hx0]
    rw [hxy, cutModel_unit_mul v a b _ hunit x, hη, one_mul]

private theorem regFn_rightTranslate_upperUnipotent (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) (e : ℂ) {f : LocalGL2 v → ℂ}
    (hf : f ∈ principalSeries2 v ![a, b]) (y : v.adicCompletion ℚ) :
    regFn v a b e (rightTranslate2 v (upperUnipotent2 v y) f) = regFn v a b e f := by
  obtain ⟨m, hm⟩ := exists_cutModel_add_eq v hla hlb y
  obtain ⟨l, hl⟩ := exists_mem_levelBall v y
  obtain ⟨R, k, hT⟩ := exists_isSchwartz_tailFn v hla hlb hf
  obtain ⟨k', hS⟩ := exists_isSchwartz_cutModel_sub v hla hlb 0 m
  set S := cutModel v a b 0 - cutModel v a b m with hSdef
  set c := constTerm v a f with hcdef
  have hsplit : tailFn v a b (rightTranslate2 v (upperUnipotent2 v y) f) =
      (fun x => tailFn v a b f (x + y)) + fun x => c * (S (x + y) - S x) := by
    funext x
    rw [Pi.add_apply, tailFn_apply, tailFn_apply, lineFn_rightTranslate_upperUnipotent,
      constTerm_rightTranslate_upperUnipotent v ![a, b] a hf, hSdef, Pi.sub_apply, Pi.sub_apply, hm x, ← hcdef]
    ring
  have hT' := IsSchwartz.translate v hT hl
  have hS' := IsSchwartz.smul v (IsSchwartz.sub v (IsSchwartz.translate v hS hl) hS) c
  have hS'' : (fun x => c * ((fun x => S (x + y)) - S) x) = fun x => c * (S (x + y) - S x) := by
    funext x
    rw [Pi.sub_apply]
  rw [hS''] at hS'
  unfold regFn
  rw [hsplit, csInt_add v hT' hS', csInt_translate v hT y, constTerm_rightTranslate_upperUnipotent v ![a, b] a hf,
    ← hcdef]
  have hzero : csInt v (fun x => c * (S (x + y) - S x)) = 0 := by
    rw [← hS'', csInt_smul v (IsSchwartz.sub v (IsSchwartz.translate v hS hl) hS),
      csInt_sub v (IsSchwartz.translate v hS hl) hS, csInt_translate v hS y, sub_self, mul_zero]
  rw [hzero, add_zero]

end LanglandsTunnell.CubicInduction.LevelLattice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace LevelLattice
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

private theorem regFn_rightTranslate_diagonal2 (v : HeightOneSpectrum (𝓞 ℚ)) {a b : (v.adicCompletion ℚ)ˣ →* ℂˣ}
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) {e : ℂ}
    (he : ∀ (c : (v.adicCompletion ℚ)ˣ) (n : ℤ), Valued.v (c : v.adicCompletion ℚ) = WithZero.exp n →
      csInt v (cutModel v a b (-n) - cutModel v a b 0) = (((ratioChar v a b c : ℂˣ) : ℂ)⁻¹ - 1) * e)
    {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v ![a, b]) (d : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    regFn v a b e (rightTranslate2 v (diagonal2 v d) f) =
      torusChar2 v ![b, a] d * halfModulus2 v d * regFn v a b e f := by
  obtain ⟨cu, hcu⟩ : ∃ cu : (v.adicCompletion ℚ)ˣ, cu = d 1 * (d 0)⁻¹ := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ := exists_valued_eq_exp v cu.ne_zero
  obtain ⟨R, k, hT⟩ := exists_isSchwartz_tailFn v hla hlb hf
  obtain ⟨k', hD⟩ := exists_isSchwartz_cutModel_sub v hla hlb (-n) 0
  have hd0 : (d 0 : v.adicCompletion ℚ) ≠ 0 := (d 0).ne_zero
  have hnc : ((‖(cu : v.adicCompletion ℚ)‖ : ℝ) : ℂ) * ((‖(cu : v.adicCompletion ℚ)‖ : ℝ) : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr cu.ne_zero))
  obtain ⟨A, hA⟩ : ∃ A : v.adicCompletion ℚ → ℂ, A = fun x =>
      ((ratioChar v a b cu : ℂˣ) : ℂ)⁻¹ * ((‖(cu : v.adicCompletion ℚ)‖ : ℝ) : ℂ) *
        tailFn v a b f ((cu : v.adicCompletion ℚ) * x) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : v.adicCompletion ℚ → ℂ,
      B = fun x => constTerm v a f * (cutModel v a b (-n) - cutModel v a b 0) x := ⟨_, rfl⟩
  have hsplit : tailFn v a b (rightTranslate2 v (diagonal2 v d) f) =
      fun x => torusChar2 v ![a, b] d * halfModulus2 v d * (A + B) x := by
    funext x
    have hy : (d 0 : v.adicCompletion ℚ) * ((cu : v.adicCompletion ℚ) * x) = x * (d 1 : v.adicCompletion ℚ) := by
      rw [hcu, Units.val_mul, Units.val_inv_eq_inv_val]
      linear_combination ((d 1 : v.adicCompletion ℚ) * x) * mul_inv_cancel₀ hd0
    simp only [Pi.add_apply, hA, hB, tailFn_apply, Pi.sub_apply]
    rw [lineFn_rightTranslate_diagonal2 v ![a, b] hf d hy, constTerm_rightTranslate_diagonal2 v ![a, b] a hf d,
      torus_const_swap v a b d, ← hcu, ← cutModel_zero_mul_eq v a b hn x]
    ring
  have hA' : IsSchwartz v (R - n) (k - n) A := by
    rw [hA]
    exact IsSchwartz.smul v (IsSchwartz.dilate v hT hn) _
  have hB' : IsSchwartz v (max (-n) 0) k' B := by
    rw [hB]
    exact IsSchwartz.smul v hD _
  have hIA : csInt v A = ((ratioChar v a b cu : ℂˣ) : ℂ)⁻¹ * ((‖(cu : v.adicCompletion ℚ)‖ : ℝ) : ℂ) *
      (((‖(cu : v.adicCompletion ℚ)‖ : ℝ) : ℂ)⁻¹ * csInt v (tailFn v a b f)) := by
    rw [hA, csInt_smul v (IsSchwartz.dilate v hT hn), csInt_dilate v hT hn, Complex.ofReal_inv]
  have hIB : csInt v B = constTerm v a f * ((((ratioChar v a b cu : ℂˣ) : ℂ)⁻¹ - 1) * e) := by
    rw [hB, csInt_smul v hD, he cu n hn]
  unfold regFn
  rw [hsplit, csInt_smul v (IsSchwartz.add v hA' hB'), csInt_add v hA' hB', hIA, hIB,
    constTerm_rightTranslate_diagonal2 v ![a, b] a hf d, torus_const_ratio v a b d, ← hcu]
  linear_combination
    (torusChar2 v ![a, b] d * halfModulus2 v d * ((ratioChar v a b cu : ℂˣ) : ℂ)⁻¹ * csInt v (tailFn v a b f)) * hnc

private theorem linePt_zero_mul_antidiagonal2 (v : HeightOneSpectrum (𝓞 ℚ)) : linePt v 0 * antidiagonal2 v = 1 := by
  unfold linePt
  rw [upperUnipotent2_zero, mul_one, antidiagonal2_mul_self]

private theorem eventually_lineFn_rightTranslate_eq (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v ![a, b]) (g₀ : LocalGL2 v) :
    ∀ᶠ g in nhds g₀, lineFn v (rightTranslate2 v g f) = lineFn v (rightTranslate2 v g₀ f) ∧
      rightTranslate2 v g f 1 = rightTranslate2 v g₀ f 1 := by
  have hlc : IsLocallyConstant f := (mem_principalSeries2_iff.mp hf).1
  have h₁ : Continuous fun z : LocalGL2 v × v.adicCompletion ℚ => linePt v z.2 * z.1 :=
    ((continuous_linePt v).comp continuous_snd).mul continuous_fst
  have h₂ : Continuous fun z : LocalGL2 v × v.adicCompletion ℚ => linePt v z.2 * antidiagonal2 v * z.1 :=
    (((continuous_linePt v).comp continuous_snd).mul continuous_const).mul continuous_fst
  have h₁' : Continuous fun z : LocalGL2 v × v.adicCompletion ℚ => linePt v z.2 * g₀ :=
    ((continuous_linePt v).comp continuous_snd).mul continuous_const
  have h₂' : Continuous fun z : LocalGL2 v × v.adicCompletion ℚ => linePt v z.2 * antidiagonal2 v * g₀ :=
    (((continuous_linePt v).comp continuous_snd).mul continuous_const).mul continuous_const
  have htube : ∀ᶠ g in nhds g₀, ∀ x ∈ (levelBall (F := v.adicCompletion ℚ) 0 : Set (v.adicCompletion ℚ)),
      f (linePt v x * g) = f (linePt v x * g₀) ∧
        f (linePt v x * antidiagonal2 v * g) = f (linePt v x * antidiagonal2 v * g₀) := by
    refine (isCompact_levelBall v 0).eventually_forall_of_forall_eventually fun x _ => ?_
    filter_upwards [(h₁.tendsto (g₀, x)).eventually (hlc.eventually_eq _),
      (h₁'.tendsto (g₀, x)).eventually (hlc.eventually_eq _), (h₂.tendsto (g₀, x)).eventually (hlc.eventually_eq _),
      (h₂'.tendsto (g₀, x)).eventually (hlc.eventually_eq _)] with z e₁ e₁' e₂ e₂'
    exact ⟨e₁.trans e₁'.symm, e₂.trans e₂'.symm⟩
  refine htube.mono fun g hg => ⟨funext fun x => ?_, ?_⟩
  · by_cases hx : x ∈ levelBall (F := v.adicCompletion ℚ) 0
    · unfold lineFn
      simp only [rightTranslate2_apply]
      exact (hg x hx).1
    · have hxne : x ≠ 0 := fun h => hx (by rw [h]; exact (levelBall (F := v.adicCompletion ℚ) 0).zero_mem)
      have hinv : x⁻¹ ∈ levelBall (F := v.adicCompletion ℚ) 0 :=
        inv_mem_levelBall_of_notMem v fun h => hx (levelBall_mono (by omega) h)
      rw [lineFn_eq_of_ne_zero v ![a, b] (rightTranslate2_mem_principalSeries2 hf g) hxne,
        lineFn_eq_of_ne_zero v ![a, b] (rightTranslate2_mem_principalSeries2 hf g₀) hxne]
      congr 1
      unfold lineFn
      simp only [rightTranslate2_apply]
      exact (hg x⁻¹ hinv).2
  · have h := (hg 0 (levelBall (F := v.adicCompletion ℚ) 0).zero_mem).2
    rw [linePt_zero_mul_antidiagonal2] at h
    rw [rightTranslate2_apply, rightTranslate2_apply]
    exact h

private theorem isLocallyConstant_regFn_rightTranslate (v : HeightOneSpectrum (𝓞 ℚ))
    (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) (e : ℂ) {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v ![a, b]) :
    IsLocallyConstant fun g : LocalGL2 v => regFn v a b e (rightTranslate2 v g f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  filter_upwards [eventually_lineFn_rightTranslate_eq v a b hf g₀] with g hg
  show regFn v a b e (rightTranslate2 v g f) = regFn v a b e (rightTranslate2 v g₀ f)
  have hc : constTerm v a (rightTranslate2 v g f) = constTerm v a (rightTranslate2 v g₀ f) := by
    unfold constTerm
    rw [hg.2]
  have ht : tailFn v a b (rightTranslate2 v g f) = tailFn v a b (rightTranslate2 v g₀ f) := by
    unfold tailFn
    rw [hg.1, hc]
  unfold regFn
  rw [ht, hc]

private theorem regFn_cellSection2 (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) (e : ℂ) :
    regFn v a b e (cellSection2 v ![a, b]) = TateLocal.charExt a (-1 : v.adicCompletion ℚ) := by
  have hc : constTerm v a (cellSection2 v ![a, b]) = 0 := by
    unfold constTerm
    rw [cellSection2_one, mul_zero]
  have ht : tailFn v a b (cellSection2 v ![a, b]) =
      Set.indicator (levelBall (F := v.adicCompletion ℚ) 0 : Set (v.adicCompletion ℚ))
        fun _ => TateLocal.charExt a (-1 : v.adicCompletion ℚ) := by
    funext x
    rw [tailFn_apply, hc, zero_mul, sub_zero, lineFn_cellSection2]
    simp only [Matrix.cons_val_zero]
  unfold regFn
  rw [ht, hc, zero_mul, add_zero, csInt_indicator_const]
  unfold ballWeight
  rw [neg_zero, zpow_zero, Complex.ofReal_one, one_mul]

private theorem exists_intertwining_functional (v : HeightOneSpectrum (𝓞 ℚ)) (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) (hab : a ≠ b) :
    ∃ lam : ↥(principalSeries2 v ![a, b]) →ₗ[ℂ] ℂ,
      (∀ (x : v.adicCompletion ℚ) (ψ : ↥(principalSeries2 v ![a, b])),
          lam (principalSeries2Rep (v := v) ![a, b] (upperUnipotent2 v x) ψ) = lam ψ) ∧
        (∀ (a' : Fin 2 → (v.adicCompletion ℚ)ˣ) (ψ : ↥(principalSeries2 v ![a, b])),
          lam (principalSeries2Rep (v := v) ![a, b] (diagonal2 v a') ψ) =
            torusChar2 v ![b, a] a' * halfModulus2 v a' * lam ψ) ∧
        (∀ φ : ↥(principalSeries2 v ![a, b]),
          IsLocallyConstant fun g : LocalGL2 v => lam (principalSeries2Rep (v := v) ![a, b] g φ)) ∧
        ∃ φ : ↥(principalSeries2 v ![a, b]), lam φ ≠ 0 := by
  obtain ⟨e, he⟩ := exists_model_constant v hla hlb hab
  let lam : ↥(principalSeries2 v ![a, b]) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => regFn v a b e (ψ : LocalGL2 v → ℂ)
      map_add' := fun ψ ψ' => by
        simp only [Submodule.coe_add]
        exact regFn_add v hla hlb e ψ.2 ψ'.2
      map_smul' := fun z ψ => by
        simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
        exact regFn_smul v hla hlb e ψ.2 z }
  have hlam : ∀ ψ : ↥(principalSeries2 v ![a, b]), lam ψ = regFn v a b e (ψ : LocalGL2 v → ℂ) := fun _ => rfl
  have hrep : ∀ (g : LocalGL2 v) (ψ : ↥(principalSeries2 v ![a, b])),
      ((principalSeries2Rep (v := v) ![a, b] g ψ : ↥(principalSeries2 v ![a, b])) : LocalGL2 v → ℂ) =
        rightTranslate2 v g (ψ : LocalGL2 v → ℂ) :=
    fun _ _ => rfl
  have hm1 : (-1 : v.adicCompletion ℚ) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  refine ⟨lam, fun x ψ => ?_, fun d ψ => ?_, fun φ => ?_, ?_⟩
  · rw [hlam, hlam, hrep, regFn_rightTranslate_upperUnipotent v hla hlb e ψ.2]
  · rw [hlam, hlam, hrep, regFn_rightTranslate_diagonal2 v hla hlb he ψ.2]
  · simp only [hlam, hrep]
    exact isLocallyConstant_regFn_rightTranslate v a b e φ.2
  · refine ⟨⟨cellSection2 v ![a, b], cellSection2_mem_principalSeries2 v ![a, b] fun i => ?_⟩, ?_⟩
    · fin_cases i <;> simp [hla, hlb]
    · rw [hlam]
      show regFn v a b e (cellSection2 v ![a, b]) ≠ 0
      rw [regFn_cellSection2 v a b e, TateLocal.charExt_of_ne_zero _ hm1]
      exact Units.ne_zero _

end LanglandsTunnell.CubicInduction.LevelLattice
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace PrincipalSeriesPermutation
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel Filter Topology

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def _root_.LanglandsTunnell.CubicInduction.PrincipalSeriesPermutation.translate (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 v)
    (f : ↥(principalSeries3 v χ)) : ↥(principalSeries3 v χ) :=
  ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩

p2m_export "LanglandsTunnell.CubicInduction.PrincipalSeriesPermutation" "translate"
private theorem translate_apply (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 v)
    (f : ↥(principalSeries3 v χ)) (h : LocalGL3 v) :
    (translate v χ g f : LocalGL3 v → ℂ) h = (f : LocalGL3 v → ℂ) (h * g) := rfl

private theorem translate_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g k : LocalGL3 v)
    (f : ↥(principalSeries3 v χ)) : translate v χ (g * k) f = translate v χ g (translate v χ k f) :=
  Subtype.ext (funext fun h => show (f : LocalGL3 v → ℂ) (h * (g * k)) = (f : LocalGL3 v → ℂ) (h * g * k) by
    rw [mul_assoc])

private theorem translate_one (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (f : ↥(principalSeries3 v χ)) :
    translate v χ 1 f = f :=
  Subtype.ext (funext fun h => show (f : LocalGL3 v → ℂ) (h * 1) = (f : LocalGL3 v → ℂ) h by rw [mul_one])

private theorem translate_add (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 v)
    (f₁ f₂ : ↥(principalSeries3 v χ)) : translate v χ g (f₁ + f₂) = translate v χ g f₁ + translate v χ g f₂ :=
  Subtype.ext (map_add (gl3AmbientRightTranslate (R := ℂ) g) _ _)

private theorem translate_smul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 v) (c : ℂ)
    (f : ↥(principalSeries3 v χ)) : translate v χ g (c • f) = c • translate v χ g f :=
  Subtype.ext (map_smul (gl3AmbientRightTranslate (R := ℂ) g) c _)

private theorem isLocallyConstant_of_eventually_mul_eq {F : LocalGL3 v → ℂ}
    (h : ∀ᶠ k in 𝓝 (1 : LocalGL3 v), ∀ g : LocalGL3 v, F (g * k) = F g) : IsLocallyConstant F := by
  refine (IsLocallyConstant.iff_eventually_eq F).mpr fun g => ?_
  have ht : Tendsto (fun y : LocalGL3 v => g⁻¹ * y) (𝓝 g) (𝓝 1) :=
    (continuous_const_mul g⁻¹).tendsto' g 1 (inv_mul_cancel g)
  filter_upwards [ht.eventually h] with y hy
  have hy' := hy g
  rwa [mul_inv_cancel_left] at hy'

private theorem gl3Entry_one (i j : Fin 3) :
    gl3Entry v 1 i j = (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j := by
  simp only [gl3Entry, Units.val_one]

private theorem eventually_congruent (n : ℕ) :
    ∀ᶠ k in 𝓝 (1 : LocalGL3 v), ∀ i j : Fin 3,
      Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤
        WithZero.exp (-(n : ℤ)) := by
  have hc0 : (uniformizerUnit ℚ v : v.adicCompletion ℚ) ^ n ≠ 0 := pow_ne_zero _ (uniformizerUnit ℚ v).ne_zero
  have hc : Valued.v ((uniformizerUnit ℚ v : v.adicCompletion ℚ) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, valued_uniformizerUnit, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]
  refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
  have ht : Tendsto
      (fun k : LocalGL3 v => gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
      (𝓝 1) (𝓝 0) :=
    ((continuous_gl3Entry v i j).fun_sub continuous_const).tendsto' 1 0 (by simp only [gl3Entry_one, sub_self])
  filter_upwards [ht.eventually (eventually_valued_lt v hc0)] with k hk
  rw [hc] at hk
  exact hk.le

private theorem eventually_translate_eq (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : ↥(principalSeries3 v χ)) : ∀ᶠ k in 𝓝 (1 : LocalGL3 v), translate v χ k f = f := by
  obtain ⟨n, hn⟩ := exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ f f.2
  filter_upwards [eventually_congruent v n] with k hk
  exact Subtype.ext (hn k hk)

private theorem rpow_half_div_mul_sqrt_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℝ) :
    (x * y) ^ ((1 : ℝ) / 2) / z * Real.sqrt (x / y) = x / z := by
  rw [← Real.sqrt_eq_rpow, div_mul_eq_mul_div, ← Real.sqrt_mul (mul_nonneg hx.le hy.le),
    show x * y * (x / y) = x * x * (y / y) by ring, div_self hy.ne', mul_one, Real.sqrt_mul_self hx.le]

private theorem mul_rpow_neg_half_mul_sqrt_div (x : ℝ) {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    x * (y * z) ^ (-((1 : ℝ) / 2)) * Real.sqrt (y / z) = x / z := by
  rw [Real.rpow_neg (mul_nonneg hy.le hz.le), ← Real.sqrt_eq_rpow, mul_assoc, ← div_eq_inv_mul,
    ← Real.sqrt_div' _ (mul_nonneg hy.le hz.le),
    show y / z / (y * z) = 1 / z * (1 / z) * (y / y) by ring, div_self hy.ne', mul_one,
    Real.sqrt_mul_self (one_div_nonneg.mpr hz.le), ← div_eq_mul_one_div]

private theorem restrictLin_translate_upperUnipotent3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (x y z : v.adicCompletion ℚ) (F : ↥(principalSeries3 v χ)) :
    restrictLin v χ (translate v χ (upperUnipotent3 x y z) F) =
      (principalSeries2Rep (v := v) ![χ 0, χ 1]) (upperUnipotent2 v x) (restrictLin v χ F) := by
  have h := restrictLin_rightTranslate v χ (upperUnipotent3 x y z) (upperUnipotent2 v x) 1 F
    (by simp [upperUnipotent3_coe]) (by simp [upperUnipotent3_coe]) (by simp [upperUnipotent3_coe])
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [upperUnipotent3_coe, upperUnipotent2_coe])
  have hdet : ((upperUnipotent2 v x : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
    simp [upperUnipotent2_coe, Matrix.det_fin_two]
  rw [hdet, Units.val_one, norm_one, Real.one_rpow, div_one, Complex.ofReal_one, one_smul, map_one,
    Units.val_one, one_smul] at h
  exact h

private theorem restrictLowLin_translate_upperUnipotent3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (x y z : v.adicCompletion ℚ) (F : ↥(principalSeries3 v χ)) :
    restrictLowLin v χ (translate v χ (upperUnipotent3 x y z) F) =
      (principalSeries2Rep (v := v) ![χ 1, χ 2]) (upperUnipotent2 v y) (restrictLowLin v χ F) := by
  have h := restrictLowLin_rightTranslate v χ (upperUnipotent3 x y z) (upperUnipotent2 v y) 1 F
    (by simp [upperUnipotent3_coe]) (by simp [upperUnipotent3_coe]) (by simp [upperUnipotent3_coe])
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [upperUnipotent3_coe, upperUnipotent2_coe])
  have hdet : ((upperUnipotent2 v y : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
    simp [upperUnipotent2_coe, Matrix.det_fin_two]
  rw [hdet, Units.val_one, norm_one, Real.one_rpow, mul_one, Complex.ofReal_one, one_smul, map_one,
    Units.val_one, one_smul] at h
  exact h

private theorem restrictLin_translate_diagonal3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (F : ↥(principalSeries3 v χ)) :
    restrictLin v χ (translate v χ (diagonal3 v a) F) =
      (((‖(a 0 : v.adicCompletion ℚ)‖ * ‖(a 1 : v.adicCompletion ℚ)‖) ^ ((1 : ℝ) / 2) /
          ‖(a 2 : v.adicCompletion ℚ)‖ : ℝ) : ℂ) •
        ((((χ 2) (a 2) : ℂˣ) : ℂ) •
          (principalSeries2Rep (v := v) ![χ 0, χ 1]) (diagonal2 v ![a 0, a 1]) (restrictLin v χ F)) := by
  have h := restrictLin_rightTranslate v χ (diagonal3 v a) (diagonal2 v ![a 0, a 1]) (a 2) F
    (by simp [diagonal3_coe, Matrix.diagonal]) (by simp [diagonal3_coe, Matrix.diagonal])
    (by simp [diagonal3_coe, Matrix.diagonal])
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [diagonal3_coe, diagonal2_coe, Matrix.diagonal])
  have hdet : ((diagonal2 v ![a 0, a 1] : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det =
      (a 0 : v.adicCompletion ℚ) * (a 1 : v.adicCompletion ℚ) := by
    simp [diagonal2_coe]
  rw [hdet, norm_mul] at h
  exact h

private theorem restrictLowLin_translate_diagonal3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (F : ↥(principalSeries3 v χ)) :
    restrictLowLin v χ (translate v χ (diagonal3 v a) F) =
      ((‖(a 0 : v.adicCompletion ℚ)‖ *
          (‖(a 1 : v.adicCompletion ℚ)‖ * ‖(a 2 : v.adicCompletion ℚ)‖) ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) •
        ((((χ 0) (a 0) : ℂˣ) : ℂ) •
          (principalSeries2Rep (v := v) ![χ 1, χ 2]) (diagonal2 v ![a 1, a 2]) (restrictLowLin v χ F)) := by
  have h := restrictLowLin_rightTranslate v χ (diagonal3 v a) (diagonal2 v ![a 1, a 2]) (a 0) F
    (by simp [diagonal3_coe, Matrix.diagonal]) (by simp [diagonal3_coe, Matrix.diagonal])
    (by simp [diagonal3_coe, Matrix.diagonal])
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [diagonal3_coe, diagonal2_coe, Matrix.diagonal])
  have hdet : ((diagonal2 v ![a 1, a 2] : LocalGL2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det =
      (a 1 : v.adicCompletion ℚ) * (a 2 : v.adicCompletion ℚ) := by
    simp [diagonal2_coe]
  rw [hdet, norm_mul] at h
  exact h

section Upper

variable (χ χ' : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
  (M : ↥(principalSeries2 v ![χ 0, χ 1]) →ₗ[ℂ] ↥(principalSeries2 v ![χ' 0, χ' 1]))

private noncomputable def swapFn (f : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ :=
  fun g => ((M (restrictLin v χ (translate v χ g f)) : ↥(principalSeries2 v ![χ' 0, χ' 1])) :
    LocalGL2 v → ℂ) 1

private theorem swapFn_apply (f : ↥(principalSeries3 v χ)) (g : LocalGL3 v) :
    swapFn v χ χ' M f g =
      ((M (restrictLin v χ (translate v χ g f)) : ↥(principalSeries2 v ![χ' 0, χ' 1])) : LocalGL2 v → ℂ) 1 :=
  rfl

private theorem swapFn_add (f₁ f₂ : ↥(principalSeries3 v χ)) :
    swapFn v χ χ' M (f₁ + f₂) = swapFn v χ χ' M f₁ + swapFn v χ χ' M f₂ := by
  funext g
  simp only [Pi.add_apply, swapFn_apply, translate_add, map_add, Submodule.coe_add]

private theorem swapFn_smul (c : ℂ) (f : ↥(principalSeries3 v χ)) :
    swapFn v χ χ' M (c • f) = c • swapFn v χ χ' M f := by
  funext g
  simp only [Pi.smul_apply, swapFn_apply, translate_smul, map_smul, Submodule.coe_smul]

variable (hM : ∀ (m : LocalGL2 v) (φ : ↥(principalSeries2 v ![χ 0, χ 1])),
    M ((principalSeries2Rep (v := v) ![χ 0, χ 1]) m φ) = (principalSeries2Rep (v := v) ![χ' 0, χ' 1]) m (M φ))

include hM in

private theorem swapFn_mem (h2 : χ' 2 = χ 2) (f : ↥(principalSeries3 v χ)) :
    swapFn v χ χ' M f ∈ principalSeries3 v χ' := by
  refine mem_principalSeries3_iff.mpr ⟨?_, ?_, ?_⟩
  · refine isLocallyConstant_of_eventually_mul_eq v ?_
    filter_upwards [eventually_translate_eq v χ f] with k hk g
    rw [swapFn_apply, swapFn_apply, translate_mul, hk]
  · intro x y z g
    rw [swapFn_apply, swapFn_apply, translate_mul, restrictLin_translate_upperUnipotent3, hM,
      principalSeries2Rep_apply_coe, one_mul]
    have hn := (mem_principalSeries2_iff.mp (M (restrictLin v χ (translate v χ g f))).2).2.1 x 1
    rw [mul_one] at hn
    exact hn
  · intro a g
    have hx : 0 < ‖(a 0 : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr (a 0).ne_zero
    have hy : 0 < ‖(a 1 : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr (a 1).ne_zero
    have ht := (mem_principalSeries2_iff.mp (M (restrictLin v χ (translate v χ g f))).2).2.2 ![a 0, a 1] 1
    rw [mul_one] at ht
    rw [swapFn_apply, swapFn_apply, translate_mul, restrictLin_translate_diagonal3, map_smul, map_smul, hM,
      Submodule.coe_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      principalSeries2Rep_apply_coe, one_mul, ht, ← h2]
    simp only [torusChar2, torusChar3, halfModulus2, halfModulus3, Fin.prod_univ_two, Fin.prod_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show ∀ (s c₂ c₀ c₁ q X : ℂ), s * (c₂ * (c₀ * c₁ * q * X)) = s * q * (c₀ * c₁ * c₂ * X) from
        fun s c₂ c₀ c₁ q X => by ring,
      ← Complex.ofReal_mul, rpow_half_div_mul_sqrt_div hx hy]
    ring

private noncomputable def swapLin (h2 : χ' 2 = χ 2) : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ') where
  toFun f := ⟨swapFn v χ χ' M f, swapFn_mem v χ χ' M hM h2 f⟩
  map_add' f₁ f₂ := Subtype.ext (swapFn_add v χ χ' M f₁ f₂)
  map_smul' c f := Subtype.ext (swapFn_smul v χ χ' M c f)

private theorem coe_swapLin (h2 : χ' 2 = χ 2) (f : ↥(principalSeries3 v χ)) :
    (swapLin v χ χ' M hM h2 f : LocalGL3 v → ℂ) = swapFn v χ χ' M f := rfl

private theorem swapLin_translate (h2 : χ' 2 = χ 2) (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)) :
    swapLin v χ χ' M hM h2 (translate v χ g f) = translate v χ' g (swapLin v χ χ' M hM h2 f) :=
  Subtype.ext (funext fun h => by
    rw [coe_swapLin, translate_apply, coe_swapLin, swapFn_apply, swapFn_apply, translate_mul])

private theorem restrictLin_translate_swapLin (h2 : χ' 2 = χ 2) (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)) :
    restrictLin v χ' (translate v χ' g (swapLin v χ χ' M hM h2 f)) = M (restrictLin v χ (translate v χ g f)) := by
  refine Subtype.ext (funext fun m => ?_)
  have hp : restrictLin v χ (translate v χ (iotaGL m) (translate v χ g f)) =
      ((‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ) •
        (principalSeries2Rep (v := v) ![χ 0, χ 1]) m (restrictLin v χ (translate v χ g f)) := by
    have h := restrictLin_rightTranslate v χ (iotaGL m) m 1 (translate v χ g f)
      (by simp [coe_iotaGL, embedMat2]) (by simp [coe_iotaGL, embedMat2]) (by simp [coe_iotaGL, embedMat2])
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [coe_iotaGL, embedMat2])
    rw [Units.val_one, norm_one, div_one, map_one, Units.val_one, one_smul] at h
    exact h
  have hnorm : leviNorm v m *
      (((‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) = 1 := by
    unfold leviNorm
    rw [mul_comm]
    exact det_rpow_half_mul_neg_half v m
  rw [restrictLin_apply_coe]
  show leviNorm v m * swapFn v χ χ' M f (iotaGL m * g) = _
  rw [swapFn_apply, translate_mul, hp, map_smul, hM, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    principalSeries2Rep_apply_coe, one_mul, ← mul_assoc, hnorm, one_mul]

end Upper
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

section Lower

variable (χ χ' : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
  (M : ↥(principalSeries2 v ![χ 1, χ 2]) →ₗ[ℂ] ↥(principalSeries2 v ![χ' 1, χ' 2]))

private noncomputable def swapLowFn (f : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ :=
  fun g => ((M (restrictLowLin v χ (translate v χ g f)) : ↥(principalSeries2 v ![χ' 1, χ' 2])) :
    LocalGL2 v → ℂ) 1

private theorem swapLowFn_apply (f : ↥(principalSeries3 v χ)) (g : LocalGL3 v) :
    swapLowFn v χ χ' M f g =
      ((M (restrictLowLin v χ (translate v χ g f)) : ↥(principalSeries2 v ![χ' 1, χ' 2])) : LocalGL2 v → ℂ) 1 :=
  rfl

private theorem swapLowFn_add (f₁ f₂ : ↥(principalSeries3 v χ)) :
    swapLowFn v χ χ' M (f₁ + f₂) = swapLowFn v χ χ' M f₁ + swapLowFn v χ χ' M f₂ := by
  funext g
  simp only [Pi.add_apply, swapLowFn_apply, translate_add, map_add, Submodule.coe_add]

private theorem swapLowFn_smul (c : ℂ) (f : ↥(principalSeries3 v χ)) :
    swapLowFn v χ χ' M (c • f) = c • swapLowFn v χ χ' M f := by
  funext g
  simp only [Pi.smul_apply, swapLowFn_apply, translate_smul, map_smul, Submodule.coe_smul]

variable (hM : ∀ (m : LocalGL2 v) (φ : ↥(principalSeries2 v ![χ 1, χ 2])),
    M ((principalSeries2Rep (v := v) ![χ 1, χ 2]) m φ) = (principalSeries2Rep (v := v) ![χ' 1, χ' 2]) m (M φ))

include hM in

private theorem swapLowFn_mem (h0 : χ' 0 = χ 0) (f : ↥(principalSeries3 v χ)) :
    swapLowFn v χ χ' M f ∈ principalSeries3 v χ' := by
  refine mem_principalSeries3_iff.mpr ⟨?_, ?_, ?_⟩
  · refine isLocallyConstant_of_eventually_mul_eq v ?_
    filter_upwards [eventually_translate_eq v χ f] with k hk g
    rw [swapLowFn_apply, swapLowFn_apply, translate_mul, hk]
  · intro x y z g
    rw [swapLowFn_apply, swapLowFn_apply, translate_mul, restrictLowLin_translate_upperUnipotent3, hM,
      principalSeries2Rep_apply_coe, one_mul]
    have hn := (mem_principalSeries2_iff.mp (M (restrictLowLin v χ (translate v χ g f))).2).2.1 y 1
    rw [mul_one] at hn
    exact hn
  · intro a g
    have hy : 0 < ‖(a 1 : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr (a 1).ne_zero
    have hz : 0 < ‖(a 2 : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr (a 2).ne_zero
    have ht := (mem_principalSeries2_iff.mp (M (restrictLowLin v χ (translate v χ g f))).2).2.2 ![a 1, a 2] 1
    rw [mul_one] at ht
    rw [swapLowFn_apply, swapLowFn_apply, translate_mul, restrictLowLin_translate_diagonal3, map_smul, map_smul, hM,
      Submodule.coe_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      principalSeries2Rep_apply_coe, one_mul, ht, ← h0]
    simp only [torusChar2, torusChar3, halfModulus2, halfModulus3, Fin.prod_univ_two, Fin.prod_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show ∀ (s c₀ c₁ c₂ q X : ℂ), s * (c₀ * (c₁ * c₂ * q * X)) = s * q * (c₀ * c₁ * c₂ * X) from
        fun s c₀ c₁ c₂ q X => by ring,
      ← Complex.ofReal_mul, mul_rpow_neg_half_mul_sqrt_div _ hy hz]
    ring

private noncomputable def swapLowLin (h0 : χ' 0 = χ 0) :
    ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ') where
  toFun f := ⟨swapLowFn v χ χ' M f, swapLowFn_mem v χ χ' M hM h0 f⟩
  map_add' f₁ f₂ := Subtype.ext (swapLowFn_add v χ χ' M f₁ f₂)
  map_smul' c f := Subtype.ext (swapLowFn_smul v χ χ' M c f)

private theorem coe_swapLowLin (h0 : χ' 0 = χ 0) (f : ↥(principalSeries3 v χ)) :
    (swapLowLin v χ χ' M hM h0 f : LocalGL3 v → ℂ) = swapLowFn v χ χ' M f := rfl

private theorem swapLowLin_translate (h0 : χ' 0 = χ 0) (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)) :
    swapLowLin v χ χ' M hM h0 (translate v χ g f) = translate v χ' g (swapLowLin v χ χ' M hM h0 f) :=
  Subtype.ext (funext fun h => by
    rw [coe_swapLowLin, translate_apply, coe_swapLowLin, swapLowFn_apply, swapLowFn_apply, translate_mul])

private theorem restrictLowLin_translate_swapLowLin (h0 : χ' 0 = χ 0) (g : LocalGL3 v)
    (f : ↥(principalSeries3 v χ)) :
    restrictLowLin v χ' (translate v χ' g (swapLowLin v χ χ' M hM h0 f)) =
      M (restrictLowLin v χ (translate v χ g f)) := by
  refine Subtype.ext (funext fun m => ?_)
  have hp : restrictLowLin v χ (translate v χ (iotaLow v m) (translate v χ g f)) =
      ((‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ) •
        (principalSeries2Rep (v := v) ![χ 1, χ 2]) m (restrictLowLin v χ (translate v χ g f)) := by
    have h := restrictLowLin_rightTranslate v χ (iotaLow v m) m 1 (translate v χ g f)
      (by simp [coe_iotaLow, embedLow]) (by simp [coe_iotaLow, embedLow]) (by simp [coe_iotaLow, embedLow])
      (by intro i j; fin_cases i <;> fin_cases j <;> simp [coe_iotaLow, embedLow])
    rw [Units.val_one, norm_one, one_mul, map_one, Units.val_one, one_smul] at h
    exact h
  have hnorm : leviNormLow v m *
      (((‖(m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ (-((1 : ℝ) / 2)) : ℝ) : ℂ)) = 1 := by
    unfold leviNormLow
    exact det_rpow_half_mul_neg_half v m
  rw [restrictLowLin_apply_coe]
  show leviNormLow v m * swapLowFn v χ χ' M f (iotaLow v m * g) = _
  rw [swapLowFn_apply, translate_mul, hp, map_smul, hM, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    principalSeries2Rep_apply_coe, one_mul, ← mul_assoc, hnorm, one_mul]

end Lower
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

private def HasEquivariantEquiv (χ ψ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : Prop :=
  ∃ Φ : ↥(principalSeries3 v χ) ≃ₗ[ℂ] ↥(principalSeries3 v ψ),
    ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)), Φ (translate v χ g f) = translate v ψ g (Φ f)

private theorem hasEquivariantEquiv_of_eq {χ ψ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} (h : χ = ψ) :
    HasEquivariantEquiv v χ ψ := by
  subst h
  exact ⟨LinearEquiv.refl ℂ _, fun _ _ => rfl⟩

private theorem HasEquivariantEquiv.trans {χ ψ ω : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (h₁ : HasEquivariantEquiv v χ ψ) (h₂ : HasEquivariantEquiv v ψ ω) : HasEquivariantEquiv v χ ω := by
  obtain ⟨Φ₁, hΦ₁⟩ := h₁
  obtain ⟨Φ₂, hΦ₂⟩ := h₂
  exact ⟨Φ₁.trans Φ₂, fun g f => by rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hΦ₁, hΦ₂]⟩

private def IsIntertwinerPair (ψ ψ' : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (M : ↥(principalSeries2 v ψ) →ₗ[ℂ] ↥(principalSeries2 v ψ'))
    (M' : ↥(principalSeries2 v ψ') →ₗ[ℂ] ↥(principalSeries2 v ψ)) : Prop :=
  (∀ (m : LocalGL2 v) (φ : ↥(principalSeries2 v ψ)),
      M ((principalSeries2Rep (v := v) ψ) m φ) = (principalSeries2Rep (v := v) ψ') m (M φ)) ∧
    (∀ (m : LocalGL2 v) (φ' : ↥(principalSeries2 v ψ')),
      M' ((principalSeries2Rep (v := v) ψ') m φ') = (principalSeries2Rep (v := v) ψ) m (M' φ')) ∧
    (∀ φ : ↥(principalSeries2 v ψ), M' (M φ) = φ) ∧ ∀ φ' : ↥(principalSeries2 v ψ'), M (M' φ') = φ'

private theorem restrictLin_translate_apply_one (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 v)
    (f : ↥(principalSeries3 v χ)) :
    ((restrictLin v χ (translate v χ g f) : ↥(principalSeries2 v ![χ 0, χ 1])) : LocalGL2 v → ℂ) 1 =
      (f : LocalGL3 v → ℂ) g := by
  rw [restrictLin_apply_of_det_eq_one v χ (translate v χ g f) 1 (by rw [Units.val_one, Matrix.det_one]), map_one,
    translate_apply, one_mul]

private theorem restrictLowLin_translate_apply_one (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 v)
    (f : ↥(principalSeries3 v χ)) :
    ((restrictLowLin v χ (translate v χ g f) : ↥(principalSeries2 v ![χ 1, χ 2])) : LocalGL2 v → ℂ) 1 =
      (f : LocalGL3 v → ℂ) g := by
  rw [restrictLowLin_apply_of_det_eq_one v χ (translate v χ g f) 1 (by rw [Units.val_one, Matrix.det_one]),
    map_one, translate_apply, one_mul]

private theorem hasEquivariantEquiv_of_upper (χ χ' : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (h2 : χ' 2 = χ 2)
    (M : ↥(principalSeries2 v ![χ 0, χ 1]) →ₗ[ℂ] ↥(principalSeries2 v ![χ' 0, χ' 1]))
    (M' : ↥(principalSeries2 v ![χ' 0, χ' 1]) →ₗ[ℂ] ↥(principalSeries2 v ![χ 0, χ 1]))
    (hMM' : IsIntertwinerPair v ![χ 0, χ 1] ![χ' 0, χ' 1] M M') : HasEquivariantEquiv v χ χ' := by
  obtain ⟨hM, hM', hinv, hinv'⟩ := hMM'
  refine ⟨{ swapLin v χ χ' M hM h2 with
      invFun := swapLin v χ' χ M' hM' h2.symm
      left_inv := fun f => Subtype.ext (funext fun g => ?_)
      right_inv := fun f' => Subtype.ext (funext fun g => ?_) }, fun g f => swapLin_translate v χ χ' M hM h2 g f⟩
  · show swapFn v χ' χ M' (swapLin v χ χ' M hM h2 f) g = (f : LocalGL3 v → ℂ) g
    rw [swapFn_apply, restrictLin_translate_swapLin, hinv, restrictLin_translate_apply_one]
  · show swapFn v χ χ' M (swapLin v χ' χ M' hM' h2.symm f') g = (f' : LocalGL3 v → ℂ) g
    rw [swapFn_apply, restrictLin_translate_swapLin, hinv', restrictLin_translate_apply_one]

private theorem hasEquivariantEquiv_of_lower (χ χ' : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (h0 : χ' 0 = χ 0)
    (M : ↥(principalSeries2 v ![χ 1, χ 2]) →ₗ[ℂ] ↥(principalSeries2 v ![χ' 1, χ' 2]))
    (M' : ↥(principalSeries2 v ![χ' 1, χ' 2]) →ₗ[ℂ] ↥(principalSeries2 v ![χ 1, χ 2]))
    (hMM' : IsIntertwinerPair v ![χ 1, χ 2] ![χ' 1, χ' 2] M M') : HasEquivariantEquiv v χ χ' := by
  obtain ⟨hM, hM', hinv, hinv'⟩ := hMM'
  refine ⟨{ swapLowLin v χ χ' M hM h0 with
      invFun := swapLowLin v χ' χ M' hM' h0.symm
      left_inv := fun f => Subtype.ext (funext fun g => ?_)
      right_inv := fun f' => Subtype.ext (funext fun g => ?_) },
    fun g f => swapLowLin_translate v χ χ' M hM h0 g f⟩
  · show swapLowFn v χ' χ M' (swapLowLin v χ χ' M hM h0 f) g = (f : LocalGL3 v → ℂ) g
    rw [swapLowFn_apply, restrictLowLin_translate_swapLowLin, hinv, restrictLowLin_translate_apply_one]
  · show swapLowFn v χ χ' M (swapLowLin v χ' χ M' hM' h0.symm f') g = (f' : LocalGL3 v → ℂ) g
    rw [swapLowFn_apply, restrictLowLin_translate_swapLowLin, hinv', restrictLowLin_translate_apply_one]

private def HasIntertwiners (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : Prop :=
  ∀ (i j : Fin 3) (ψ ψ' : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)),
    ψ = ![χ i, χ j] → ψ' = ![χ j, χ i] →
      ∃ (M : ↥(principalSeries2 v ψ) →ₗ[ℂ] ↥(principalSeries2 v ψ'))
        (M' : ↥(principalSeries2 v ψ') →ₗ[ℂ] ↥(principalSeries2 v ψ)), IsIntertwinerPair v ψ ψ' M M'

private theorem HasIntertwiners.comp {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} (h : HasIntertwiners v χ)
    (σ : Equiv.Perm (Fin 3)) : HasIntertwiners v (χ ∘ ⇑σ) :=
  fun i j ψ ψ' hψ hψ' => h (σ i) (σ j) ψ ψ' hψ hψ'

private theorem hasEquivariantEquiv_swap_zero_one {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (h : HasIntertwiners v χ) : HasEquivariantEquiv v χ (χ ∘ ⇑(Equiv.swap (0 : Fin 3) 1)) := by
  obtain ⟨M, M', hMM'⟩ := h 0 1 ![χ 0, χ 1]
    ![(χ ∘ ⇑(Equiv.swap (0 : Fin 3) 1)) 0, (χ ∘ ⇑(Equiv.swap (0 : Fin 3) 1)) 1] rfl
    (by simp [Equiv.swap_apply_left, Equiv.swap_apply_right])
  exact hasEquivariantEquiv_of_upper v χ _ (by simp [Equiv.swap_apply_of_ne_of_ne]) M M' hMM'

private theorem hasEquivariantEquiv_swap_one_two {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (h : HasIntertwiners v χ) : HasEquivariantEquiv v χ (χ ∘ ⇑(Equiv.swap (1 : Fin 3) 2)) := by
  obtain ⟨M, M', hMM'⟩ := h 1 2 ![χ 1, χ 2]
    ![(χ ∘ ⇑(Equiv.swap (1 : Fin 3) 2)) 1, (χ ∘ ⇑(Equiv.swap (1 : Fin 3) 2)) 2] rfl
    (by simp [Equiv.swap_apply_left, Equiv.swap_apply_right])
  exact hasEquivariantEquiv_of_lower v χ _ (by simp [Equiv.swap_apply_of_ne_of_ne]) M M' hMM'

private theorem swap_zero_two_eq :
    Equiv.swap (0 : Fin 3) 2 = Equiv.swap 0 1 * (Equiv.swap 1 2 * Equiv.swap 0 1) := by
  ext i
  fin_cases i <;> simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def]

private theorem hasEquivariantEquiv_swap {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (h : HasIntertwiners v χ) (x y : Fin 3) (hxy : x ≠ y) :
    HasEquivariantEquiv v χ (χ ∘ ⇑(Equiv.swap x y)) := by
  have h01 : ∀ ω : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ), HasIntertwiners v ω →
      HasEquivariantEquiv v ω (ω ∘ ⇑(Equiv.swap (0 : Fin 3) 1)) := fun ω hω => hasEquivariantEquiv_swap_zero_one v hω
  have h12 : ∀ ω : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ), HasIntertwiners v ω →
      HasEquivariantEquiv v ω (ω ∘ ⇑(Equiv.swap (1 : Fin 3) 2)) := fun ω hω => hasEquivariantEquiv_swap_one_two v hω
  have h02 : HasEquivariantEquiv v χ (χ ∘ ⇑(Equiv.swap (0 : Fin 3) 2)) := by
    rw [swap_zero_two_eq]
    exact ((h01 χ h).trans v (h12 _ (h.comp v _))).trans v (h01 _ ((h.comp v _).comp v _))
  fin_cases x <;> fin_cases y
  · exact absurd rfl hxy
  · exact h01 χ h
  · exact h02
  · rw [Equiv.swap_comm]; exact h01 χ h
  · exact absurd rfl hxy
  · exact h12 χ h
  · rw [Equiv.swap_comm]; exact h02
  · rw [Equiv.swap_comm]; exact h12 χ h
  · exact absurd rfl hxy

private theorem hasEquivariantEquiv_perm {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} (h : HasIntertwiners v χ)
    (w : Equiv.Perm (Fin 3)) : HasEquivariantEquiv v χ (χ ∘ ⇑w) :=
  Equiv.Perm.swap_induction_on' w (hasEquivariantEquiv_of_eq v (funext fun _ => by simp)) fun τ x y hxy ih =>
    ih.trans v (by
      rw [show (χ ∘ ⇑(τ * Equiv.swap x y)) = (χ ∘ ⇑τ) ∘ ⇑(Equiv.swap x y) from rfl]
      exact hasEquivariantEquiv_swap v (h.comp v τ) x y hxy)

end LanglandsTunnell.CubicInduction.PrincipalSeriesPermutation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace PrincipalSeriesPermutation
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open Matrix IsDedekindDomain NumberField LanglandsTunnell.CubicInduction.PadicTransport

variable (v : HeightOneSpectrum (𝓞 ℚ))

section Functional

variable (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ) (lam : ↥(principalSeries2 v ![a, b]) →ₗ[ℂ] ℂ)

private noncomputable def functionalFn (φ : ↥(principalSeries2 v ![a, b])) : LocalGL2 v → ℂ :=
  fun g => lam ((principalSeries2Rep (v := v) ![a, b]) g φ)

private theorem functionalFn_apply (φ : ↥(principalSeries2 v ![a, b])) (g : LocalGL2 v) :
    functionalFn v a b lam φ g = lam ((principalSeries2Rep (v := v) ![a, b]) g φ) := rfl

variable
  (hN : ∀ (x : v.adicCompletion ℚ) (ψ : ↥(principalSeries2 v ![a, b])),
    lam ((principalSeries2Rep (v := v) ![a, b]) (upperUnipotent2 v x) ψ) = lam ψ)
  (hT : ∀ (a' : Fin 2 → (v.adicCompletion ℚ)ˣ) (ψ : ↥(principalSeries2 v ![a, b])),
    lam ((principalSeries2Rep (v := v) ![a, b]) (diagonal2 v a') ψ) =
      torusChar2 v ![b, a] a' * halfModulus2 v a' * lam ψ)
  (hLC : ∀ φ : ↥(principalSeries2 v ![a, b]),
    IsLocallyConstant fun g : LocalGL2 v => lam ((principalSeries2Rep (v := v) ![a, b]) g φ))

include hN hT hLC in

private theorem functionalFn_mem (φ : ↥(principalSeries2 v ![a, b])) :
    functionalFn v a b lam φ ∈ principalSeries2 v ![b, a] := by
  refine mem_principalSeries2_iff.mpr ⟨hLC φ, fun x g => ?_, fun a' g => ?_⟩
  · rw [functionalFn_apply, functionalFn_apply, map_mul, Module.End.mul_apply, hN]
  · rw [functionalFn_apply, functionalFn_apply, map_mul, Module.End.mul_apply, hT]

private noncomputable def intertwinerOfFunctional :
    ↥(principalSeries2 v ![a, b]) →ₗ[ℂ] ↥(principalSeries2 v ![b, a]) where
  toFun φ := ⟨functionalFn v a b lam φ, functionalFn_mem v a b lam hN hT hLC φ⟩
  map_add' φ₁ φ₂ := Subtype.ext (funext fun g => by
    show lam ((principalSeries2Rep (v := v) ![a, b]) g (φ₁ + φ₂)) =
      lam ((principalSeries2Rep (v := v) ![a, b]) g φ₁) + lam ((principalSeries2Rep (v := v) ![a, b]) g φ₂)
    rw [map_add, map_add])
  map_smul' c φ := Subtype.ext (funext fun g => by
    show lam ((principalSeries2Rep (v := v) ![a, b]) g (c • φ)) = c * lam ((principalSeries2Rep (v := v) ![a, b]) g φ)
    rw [map_smul, map_smul, smul_eq_mul])

private theorem intertwinerOfFunctional_apply_coe (φ : ↥(principalSeries2 v ![a, b])) (g : LocalGL2 v) :
    ((intertwinerOfFunctional v a b lam hN hT hLC φ : ↥(principalSeries2 v ![b, a])) : LocalGL2 v → ℂ) g =
      lam ((principalSeries2Rep (v := v) ![a, b]) g φ) :=
  rfl

private theorem intertwinerOfFunctional_equivariant (m : LocalGL2 v) (φ : ↥(principalSeries2 v ![a, b])) :
    intertwinerOfFunctional v a b lam hN hT hLC ((principalSeries2Rep (v := v) ![a, b]) m φ) =
      (principalSeries2Rep (v := v) ![b, a]) m (intertwinerOfFunctional v a b lam hN hT hLC φ) :=
  Subtype.ext (funext fun g => by
    rw [principalSeries2Rep_apply_coe, intertwinerOfFunctional_apply_coe, intertwinerOfFunctional_apply_coe,
      map_mul, Module.End.mul_apply])

private theorem intertwinerOfFunctional_ne_zero (hNZ : ∃ φ : ↥(principalSeries2 v ![a, b]), lam φ ≠ 0) :
    intertwinerOfFunctional v a b lam hN hT hLC ≠ 0 := by
  obtain ⟨φ, hφ⟩ := hNZ
  intro h0
  apply hφ
  have h1 : ((intertwinerOfFunctional v a b lam hN hT hLC φ : ↥(principalSeries2 v ![b, a])) : LocalGL2 v → ℂ) 1 =
      lam φ := by
    rw [intertwinerOfFunctional_apply_coe, map_one, Module.End.one_apply]
  rw [← h1, h0, LinearMap.zero_apply, Submodule.coe_zero, Pi.zero_apply]

end Functional
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

private theorem isIrreducibleRep_of_isIrreducibleGLRep (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (h : LocalNewvector.IsIrreducibleGLRep (primeUnder v)
      (LocalNewvector.PSCarrier (primeUnder v) (charTransport v (χ 0)) (charTransport v (χ 1)))) :
    FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep (principalSeries2Rep χ) := by
  obtain ⟨⟨F, hF⟩, hW⟩ := h
  refine ⟨⟨(carrierTransport v χ).symm F, fun h0 => hF ?_⟩, fun W hWinv => ?_⟩
  · rw [← (carrierTransport v χ).apply_symm_apply F, h0, map_zero]
  · have hmap : ∀ (g' : GL (Fin 2) ℚ_[primeUnder v]) (F : LocalNewvector.PSCarrier (primeUnder v)
        (charTransport v (χ 0)) (charTransport v (χ 1))), F ∈ W.map (carrierTransport v χ).toLinearMap →
        g' • F ∈ W.map (carrierTransport v χ).toLinearMap := by
      intro g' F hF'
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hF'
      refine Submodule.mem_map.mpr ⟨principalSeries2Rep χ ((glTransport v).symm g') f, hWinv _ _ hf, ?_⟩
      rw [LinearEquiv.coe_toLinearMap, carrierTransport_principalSeries2Rep, MulEquiv.apply_symm_apply]
    have hinj : Function.Injective (Submodule.map (carrierTransport v χ).toLinearMap) :=
      Submodule.map_injective_of_injective (carrierTransport v χ).injective
    rcases hW _ hmap with hbot | htop
    · left
      apply hinj
      rw [hbot, Submodule.map_bot]
    · right
      apply hinj
      rw [htop, Submodule.map_top, LinearEquiv.range]

private theorem isLocallyConstant_charTransport (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hθ : IsLocallyConstant θ) :
    IsLocallyConstant (charTransport v θ) := by
  show IsLocallyConstant (⇑θ ∘ ⇑(Units.map (ratRingEquiv v).symm.toMonoidHom))
  exact hθ.comp_continuous (Continuous.units_map (ratRingEquiv v).symm.toMonoidHom (continuous_ratRingEquiv_symm v))

private theorem norm_charTransport (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hu : ∀ x, ‖((θ x : ℂˣ) : ℂ)‖ = 1)
    (y : ℚ_[primeUnder v]ˣ) : ‖((charTransport v θ y : ℂˣ) : ℂ)‖ = 1 := by
  rw [charTransport_apply]
  exact hu _

private theorem isIrreducibleRep_of_norm_eq_one (a b : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hua : ∀ x, ‖((a x : ℂˣ) : ℂ)‖ = 1) (hub : ∀ x, ‖((b x : ℂˣ) : ℂ)‖ = 1)
    (hla : IsLocallyConstant a) (hlb : IsLocallyConstant b) :
    FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep (principalSeries2Rep (v := v) ![a, b]) := by
  refine isIrreducibleRep_of_isIrreducibleGLRep v ![a, b] ?_
  obtain ⟨c₁, hc₁⟩ := exists_hasCharConductor_of_isLocallyConstant (primeUnder v) (charTransport v a)
    (isLocallyConstant_charTransport v a hla)
  obtain ⟨c₂, hc₂⟩ := exists_hasCharConductor_of_isLocallyConstant (primeUnder v) (charTransport v b)
    (isLocallyConstant_charTransport v b hlb)
  show LocalNewvector.IsIrreducibleGLRep (primeUnder v)
    (LocalNewvector.PSCarrier (primeUnder v) (charTransport v a) (charTransport v b))
  refine LocalNewvector.PSCarrier.isIrreducibleGLRep_of_hasCharConductor_of_ratio (primeUnder v) hc₁ hc₂
    fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have hn := congrArg (‖·‖) h
    simp only [norm_mul, norm_inv, norm_charTransport v a hua, norm_charTransport v b hub, inv_one, mul_one,
      Complex.norm_natCast] at hn
    exact (fact_prime_primeUnder v).out.one_lt.ne' (by exact_mod_cast hn.symm)
  · have hn := congrArg (‖·‖) h
    simp only [norm_mul, norm_inv, norm_charTransport v a hua, norm_charTransport v b hub, inv_one, mul_one,
      Complex.norm_natCast] at hn
    exact (fact_prime_primeUnder v).out.one_lt.ne' (by exact_mod_cast (inv_eq_one.mp hn.symm))

private theorem bijective_of_isIrreducibleRep {ψ ψ' : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (M : ↥(principalSeries2 v ψ) →ₗ[ℂ] ↥(principalSeries2 v ψ'))
    (hM : ∀ (m : LocalGL2 v) (φ : ↥(principalSeries2 v ψ)),
      M ((principalSeries2Rep (v := v) ψ) m φ) = (principalSeries2Rep (v := v) ψ') m (M φ))
    (h0 : M ≠ 0) (hψ : FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep (principalSeries2Rep (v := v) ψ))
    (hψ' : FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep (principalSeries2Rep (v := v) ψ')) :
    Function.Bijective M := by
  refine ⟨?_, ?_⟩
  · rcases hψ.2 (LinearMap.ker M) (fun m φ hφ => by
        rw [LinearMap.mem_ker] at hφ ⊢
        rw [hM, hφ, map_zero]) with hbot | htop
    · exact LinearMap.ker_eq_bot.mp hbot
    · exact absurd (LinearMap.ker_eq_top.mp htop) h0
  · rcases hψ'.2 (LinearMap.range M) (fun m φ' hφ' => by
        obtain ⟨φ, rfl⟩ := LinearMap.mem_range.mp hφ'
        exact LinearMap.mem_range.mpr ⟨(principalSeries2Rep (v := v) ψ) m φ, hM m φ⟩) with hbot | htop
    · exact absurd (LinearMap.range_eq_bot.mp hbot) h0
    · exact LinearMap.range_eq_top.mp htop

private theorem isIntertwinerPair_of_equiv {ψ ψ' : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (e : ↥(principalSeries2 v ψ) ≃ₗ[ℂ] ↥(principalSeries2 v ψ'))
    (he : ∀ (m : LocalGL2 v) (φ : ↥(principalSeries2 v ψ)),
      e ((principalSeries2Rep (v := v) ψ) m φ) = (principalSeries2Rep (v := v) ψ') m (e φ)) :
    IsIntertwinerPair v ψ ψ' e e.symm := by
  refine ⟨fun m φ => he m φ, fun m φ' => e.injective ?_, fun φ => e.symm_apply_apply φ,
    fun φ' => e.apply_symm_apply φ'⟩
  show e (e.symm ((principalSeries2Rep (v := v) ψ') m φ')) = e ((principalSeries2Rep (v := v) ψ) m (e.symm φ'))
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

private theorem hasIntertwiners_of_functionals (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hunit : ∀ i, ∀ x : (v.adicCompletion ℚ)ˣ, ‖((χ i x : ℂˣ) : ℂ)‖ = 1) (hlc : ∀ i, IsLocallyConstant (χ i))
    (hlam : ∀ i j : Fin 3, χ i ≠ χ j →
      ∃ lam : ↥(principalSeries2 v ![χ i, χ j]) →ₗ[ℂ] ℂ,
        (∀ (x : v.adicCompletion ℚ) (ψ : ↥(principalSeries2 v ![χ i, χ j])),
            lam ((principalSeries2Rep (v := v) ![χ i, χ j]) (upperUnipotent2 v x) ψ) = lam ψ) ∧
          (∀ (a' : Fin 2 → (v.adicCompletion ℚ)ˣ) (ψ : ↥(principalSeries2 v ![χ i, χ j])),
              lam ((principalSeries2Rep (v := v) ![χ i, χ j]) (diagonal2 v a') ψ) =
                torusChar2 v ![χ j, χ i] a' * halfModulus2 v a' * lam ψ) ∧
          (∀ φ : ↥(principalSeries2 v ![χ i, χ j]),
              IsLocallyConstant fun g : LocalGL2 v => lam ((principalSeries2Rep (v := v) ![χ i, χ j]) g φ)) ∧
          ∃ φ : ↥(principalSeries2 v ![χ i, χ j]), lam φ ≠ 0) :
    HasIntertwiners v χ := by
  intro i j ψ ψ' hψ hψ'
  subst hψ
  subst hψ'
  by_cases hij : χ i = χ j
  · rw [hij]
    exact ⟨LinearMap.id, LinearMap.id, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · obtain ⟨lam, hN, hT, hLC, hNZ⟩ := hlam i j hij
    have hb := bijective_of_isIrreducibleRep v (intertwinerOfFunctional v (χ i) (χ j) lam hN hT hLC)
      (intertwinerOfFunctional_equivariant v (χ i) (χ j) lam hN hT hLC)
      (intertwinerOfFunctional_ne_zero v (χ i) (χ j) lam hN hT hLC hNZ)
      (isIrreducibleRep_of_norm_eq_one v (χ i) (χ j) (hunit i) (hunit j) (hlc i) (hlc j))
      (isIrreducibleRep_of_norm_eq_one v (χ j) (χ i) (hunit j) (hunit i) (hlc j) (hlc i))
    exact ⟨_, _, isIntertwinerPair_of_equiv v (LinearEquiv.ofBijective _ hb) fun m φ => by
      rw [LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply]
      exact intertwinerOfFunctional_equivariant v (χ i) (χ j) lam hN hT hLC m φ⟩

private theorem permutationDatum_of_functionals (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hunit : ∀ i, ∀ x : (v.adicCompletion ℚ)ˣ, ‖((χ i x : ℂˣ) : ℂ)‖ = 1) (hlc : ∀ i, IsLocallyConstant (χ i))
    (hlam : ∀ i j : Fin 3, χ i ≠ χ j →
      ∃ lam : ↥(principalSeries2 v ![χ i, χ j]) →ₗ[ℂ] ℂ,
        (∀ (x : v.adicCompletion ℚ) (ψ : ↥(principalSeries2 v ![χ i, χ j])),
            lam ((principalSeries2Rep (v := v) ![χ i, χ j]) (upperUnipotent2 v x) ψ) = lam ψ) ∧
          (∀ (a' : Fin 2 → (v.adicCompletion ℚ)ˣ) (ψ : ↥(principalSeries2 v ![χ i, χ j])),
              lam ((principalSeries2Rep (v := v) ![χ i, χ j]) (diagonal2 v a') ψ) =
                torusChar2 v ![χ j, χ i] a' * halfModulus2 v a' * lam ψ) ∧
          (∀ φ : ↥(principalSeries2 v ![χ i, χ j]),
              IsLocallyConstant fun g : LocalGL2 v => lam ((principalSeries2Rep (v := v) ![χ i, χ j]) g φ)) ∧
          ∃ φ : ↥(principalSeries2 v ![χ i, χ j]), lam φ ≠ 0)
    (w : Equiv.Perm (Fin 3)) :
    ∃ Φ : ↥(principalSeries3 v χ) ≃ₗ[ℂ] ↥(principalSeries3 v (χ ∘ ⇑w)),
      ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
        (Φ ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ)
          = gl3AmbientRightTranslate (R := ℂ) g (Φ f) := by
  obtain ⟨Φ, hΦ⟩ := hasEquivariantEquiv_perm v (hasIntertwiners_of_functionals v χ hunit hlc hlam) w
  exact ⟨Φ, fun g f => congrArg Subtype.val (hΦ g f)⟩

end LanglandsTunnell.CubicInduction.PrincipalSeriesPermutation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace PrincipalSeriesPermutation
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

open IsDedekindDomain NumberField

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem permutationDatum (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hunit : ∀ i, ∀ x : (v.adicCompletion ℚ)ˣ, ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (hlc : ∀ i, IsLocallyConstant (χ i)) :
    ∀ w : Equiv.Perm (Fin 3), ∃ Φ : ↥(principalSeries3 v χ) ≃ₗ[ℂ] ↥(principalSeries3 v (χ ∘ ⇑w)),
        ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
          (Φ ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ)
            = gl3AmbientRightTranslate (R := ℂ) g (Φ f) :=
  fun w => permutationDatum_of_functionals v χ hunit hlc
    (fun i j hij => LevelLattice.exists_intertwining_functional v (χ i) (χ j) (hlc i) (hlc j) hij) w

end LanglandsTunnell.CubicInduction.PrincipalSeriesPermutation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_of_ne_zero TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Entry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul lowerMinor_upperUnipotent3_mul outerMinor_upperUnipotent3_mul lowerMinor_diagonal3_mul outerMinor_diagonal3_mul cellRatio charExt_units_mul antidiagonal3 antidiagonal3_coe isClopen_valued_le_one eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq eventually_mem_iff_of_isClopen continuous_gl3Entry continuous_lowerMinor continuous_outerMinor gl3Det_eq_bottom_expansion outerMinor_ne_zero_of_lowerMinor_eq_zero eventually_one_lt_valued_div gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL LocalGL3 exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 LocalGL2 rightTranslate2 rightTranslate2_apply diagonal2 diagonal2_coe upperUnipotent2 upperUnipotent2_coe halfModulus2 torusChar2 principalSeries2 mem_principalSeries2_iff rightTranslate2_mem_principalSeries2 principalSeries2Rep gl2Entry gl2Det gl2Det_ne_zero gl2Det_eq continuous_gl2Entry cornerEntry2 gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero cellCutoff2 cellValue2 cellSection2 cellSection2_mem_principalSeries2 antidiagonal2 antidiagonal2_coe cellSection2_antidiagonal2_ne_zero upperUnipotent2_mul upperUnipotent2_zero"
namespace ScalarCommutant
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_eq_exp~valued_mul_le_exp_iff LanglandsTunnell"

private theorem exists_eq_smul_one_of_eval_law
    {G : Type*} [Group G] {M : Type*} [Group M]
    {U : Type*} [AddCommGroup U] [Module ℂ U] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : G →* Module.End ℂ U) (π : M →* Module.End ℂ W) (ι : M →* G) (ν : M → ℂˣ) (ev : U →ₗ[ℂ] W)
    (hlaw : ∀ (m : M) (u : U), ev (ρ (ι m) u) = (ν m : ℂ) • π m (ev u))
    (hdet : ∀ u : U, (∀ g : G, ev (ρ g u) = 0) → u = 0)
    (hirr : FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep π)
    {K : Subgroup M} {w₀ : W} (hw₀ : w₀ ≠ 0) (hw₀K : ∀ k ∈ K, π k w₀ = w₀)
    (hfd : FiniteDimensional ℂ (FLT.SmoothAdmissibleSchurCommutant.fixedVectors π K))
    (hsep : ∀ T : Module.End ℂ U, (∀ g : G, ρ g * T = T * ρ g) → ∀ u : U, ev u = 0 → ev (T u) = 0)
    (T : Module.End ℂ U) (hT : ∀ g : G, ρ g * T = T * ρ g) :
    ∃ c : ℂ, T = c • (1 : Module.End ℂ U) := by
  have hTρ : ∀ (g : G) (u : U), T (ρ g u) = ρ g (T u) := fun g u => by
    simpa only [Module.End.mul_apply] using (LinearMap.congr_fun (hT g) u).symm

  have hΛlaw : ∀ (m : M) (u : U), ev (T (ρ (ι m) u)) = (ν m : ℂ) • π m (ev (T u)) := fun m u => by
    rw [hTρ, hlaw]

  have hstab : ∀ (m : M) (w : W), w ∈ LinearMap.range ev → π m w ∈ LinearMap.range ev := by
    rintro m _ ⟨u, rfl⟩
    refine ⟨(ν m : ℂ)⁻¹ • ρ (ι m) u, ?_⟩
    rw [map_smul, hlaw, smul_smul, inv_mul_cancel₀ (ν m).ne_zero, one_smul]
  rcases hirr.2 (LinearMap.range ev) hstab with hbot | htop
  ·
    have hev0 : ∀ x : U, ev x = 0 := fun x => by
      have hx : ev x ∈ LinearMap.range ev := LinearMap.mem_range_self ev x
      rw [hbot, Submodule.mem_bot] at hx
      exact hx
    refine ⟨0, LinearMap.ext fun u => ?_⟩
    rw [zero_smul, LinearMap.zero_apply]
    exact hdet (T u) fun g => hev0 _
  ·
    have hsurj : Function.Surjective ev := LinearMap.range_eq_top.mp htop
    have hker : LinearMap.ker ev ≤ LinearMap.ker (ev ∘ₗ T) := fun u hu => by
      rw [LinearMap.mem_ker] at hu ⊢
      exact hsep T hT u hu
    let φ : Module.End ℂ W :=
      ((LinearMap.ker ev).liftQ (ev ∘ₗ T) hker) ∘ₗ (ev.quotKerEquivOfSurjective hsurj).symm.toLinearMap
    have hφ : ∀ u : U, φ (ev u) = ev (T u) := fun u => by
      show (LinearMap.ker ev).liftQ (ev ∘ₗ T) hker ((ev.quotKerEquivOfSurjective hsurj).symm (ev u)) = _
      rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply, LinearMap.comp_apply]
    have hcomm : ∀ m : M, π m * φ = φ * π m := fun m => by
      refine LinearMap.ext fun w => ?_
      obtain ⟨u, rfl⟩ := hsurj w
      have hπ : π m (ev u) = (ν m : ℂ)⁻¹ • ev (ρ (ι m) u) := by
        rw [hlaw, smul_smul, inv_mul_cancel₀ (ν m).ne_zero, one_smul]
      rw [Module.End.mul_apply, Module.End.mul_apply, hφ, hπ, map_smul, hφ, hΛlaw, smul_smul,
        inv_mul_cancel₀ (ν m).ne_zero, one_smul]
    obtain ⟨c, hc⟩ :=
      FLT.SmoothAdmissibleSchurCommutant.exists_eq_smul_one_of_commute_of_fixed π hirr hcomm hw₀ hw₀K hfd

    have hΛc : ∀ x : U, ev (T x) = c • ev x := fun x => by
      rw [← hφ, hc, LinearMap.smul_apply, Module.End.one_apply]
    refine ⟨c, LinearMap.ext fun u => ?_⟩
    rw [LinearMap.smul_apply, Module.End.one_apply, ← sub_eq_zero]
    refine hdet _ fun g => ?_
    rw [map_sub, map_smul, map_sub, map_smul, ← hTρ, hΛc, sub_self]

private theorem exists_eq_smul_id_of_functionModel
    {G : Type*} [Group G] {M : Type*} [Group M] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (π : M →* Module.End ℂ W) (ι : M →* G) (ν : M → ℂˣ)
    (I : Submodule ℂ (G → W)) (hI : ∀ (g : G) (F : G → W), F ∈ I → (fun x => F (x * g)) ∈ I)
    (hlawI : ∀ F ∈ I, ∀ (m : M) (x : G), F (ι m * x) = (ν m : ℂ) • π m (F x))
    (hirr : FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep π)
    {K : Subgroup M} {w₀ : W} (hw₀ : w₀ ≠ 0) (hw₀K : ∀ k ∈ K, π k w₀ = w₀)
    (hfd : FiniteDimensional ℂ (FLT.SmoothAdmissibleSchurCommutant.fixedVectors π K))
    (hsep : ∀ T : ↥I →ₗ[ℂ] ↥I,
      (∀ (g : G) (F : ↥I), ((T ⟨fun x => (F : G → W) (x * g), hI g F F.2⟩ : ↥I) : G → W) =
        fun x => ((T F : ↥I) : G → W) (x * g)) →
      ∀ F : ↥I, (F : G → W) 1 = 0 → ((T F : ↥I) : G → W) 1 = 0)
    (T : ↥I →ₗ[ℂ] ↥I)
    (hT : ∀ (g : G) (F : ↥I), ((T ⟨fun x => (F : G → W) (x * g), hI g F F.2⟩ : ↥I) : G → W) =
      fun x => ((T F : ↥I) : G → W) (x * g)) :
    ∃ c : ℂ, T = c • LinearMap.id := by

  let ρ : G →* Module.End ℂ ↥I :=
    { toFun := fun g =>
        { toFun := fun F => ⟨fun x => (F : G → W) (x * g), hI g F F.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_one' := LinearMap.ext fun F => Subtype.ext (funext fun x => by simp)
      map_mul' := fun g h => LinearMap.ext fun F => Subtype.ext (funext fun x => by
        simp [mul_assoc]) }
  have hρ : ∀ (g : G) (F : ↥I) (x : G), ((ρ g F : ↥I) : G → W) x = (F : G → W) (x * g) :=
    fun _ _ _ => rfl

  let ev : ↥I →ₗ[ℂ] W :=
    { toFun := fun F => (F : G → W) 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ F : ↥I, ev F = (F : G → W) 1 := fun _ => rfl
  have hlaw : ∀ (m : M) (u : ↥I), ev (ρ (ι m) u) = (ν m : ℂ) • π m (ev u) := fun m u => by
    rw [hev, hρ, one_mul, hev, ← hlawI u u.2 m 1, mul_one]
  have hdet : ∀ u : ↥I, (∀ g : G, ev (ρ g u) = 0) → u = 0 := fun u hu =>
    Subtype.ext (funext fun g => by
      simpa only [hev, hρ, one_mul, ZeroMemClass.coe_zero, Pi.zero_apply] using hu g)
  have hTρ : ∀ g : G, ρ g * T = T * ρ g := fun g => LinearMap.ext fun F => Subtype.ext (by
    show (fun x => ((T F : ↥I) : G → W) (x * g)) =
      ((T ⟨fun x => (F : G → W) (x * g), hI g F F.2⟩ : ↥I) : G → W)
    exact (hT g F).symm)
  have hsep' : ∀ S : Module.End ℂ ↥I, (∀ g : G, ρ g * S = S * ρ g) →
      ∀ u : ↥I, ev u = 0 → ev (S u) = 0 := fun S hS u hu => by
    rw [hev] at hu ⊢
    refine hsep S (fun g F => ?_) u hu

    exact (congrArg (fun F : ↥I => (F : G → W)) (LinearMap.congr_fun (hS g) F)).symm
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_eval_law ρ π ι ν ev hlaw hdet hirr hw₀ hw₀K hfd hsep' T hTρ
  exact ⟨c, hc⟩

private theorem eval_kernel_stable_of_quadratic_annihilator
    {G : Type*} [Group G] {M : Type*} [Group M]
    {U : Type*} [AddCommGroup U] [Module ℂ U] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : G →* Module.End ℂ U) (π : M →* Module.End ℂ W) (ι : M →* G) (ν : M → ℂˣ) (N : Set G)
    (ev : U →ₗ[ℂ] W)
    (hevM : ∀ (m : M) (u : U), ev (ρ (ι m) u) = (ν m : ℂ) • π m (ev u))
    (hevN : ∀ n ∈ N, ∀ u : U, ev (ρ n u) = ev u)
    (z₀ : M) (hz₀ : π z₀ = 1) (μ₁ μ₂ : ℂ) (hμ₁ : (ν z₀ : ℂ) ≠ μ₁) (hμ₂ : (ν z₀ : ℂ) ≠ μ₂)
    (U₀ : Submodule ℂ U)
    (hann : ∀ u ∈ U₀, (ρ (ι z₀) - μ₁ • (1 : Module.End ℂ U)) ((ρ (ι z₀) - μ₂ • (1 : Module.End ℂ U)) u) ∈
      Submodule.span ℂ {w : U | ∃ n ∈ N, ∃ u' : U, w = ρ n u' - u'})
    (hirrQ : ∀ Y : Submodule ℂ U, U₀ ≤ Y → (∀ (m : M) (u : U), u ∈ Y → ρ (ι m) u ∈ Y) →
      (∀ n ∈ N, ∀ u : U, u ∈ Y → ρ n u ∈ Y) → Y = U₀ ∨ Y = ⊤)
    (S : Module.End ℂ U) (hS : ∀ g : G, ρ g * S = S * ρ g) :
    ∀ u : U, ev u = 0 → ev (S u) = 0 := by
  have hSρ : ∀ (g : G) (u : U), S (ρ g u) = ρ g (S u) := fun g u => by
    simpa only [Module.End.mul_apply] using (LinearMap.congr_fun (hS g) u).symm

  have hkill : ∀ Φ : U →ₗ[ℂ] W, (∀ (m : M) (u : U), Φ (ρ (ι m) u) = (ν m : ℂ) • π m (Φ u)) →
      (∀ n ∈ N, ∀ u : U, Φ (ρ n u) = Φ u) → ∀ u ∈ U₀, Φ u = 0 := by
    intro Φ hΦM hΦN u hu
    have hz : ∀ x : U, Φ (ρ (ι z₀) x) = (ν z₀ : ℂ) • Φ x := fun x => by
      rw [hΦM, hz₀, Module.End.one_apply]
    have hspan : Submodule.span ℂ {w : U | ∃ n ∈ N, ∃ u' : U, w = ρ n u' - u'} ≤ LinearMap.ker Φ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨n, hn, u', rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hΦN n hn, sub_self]
    have h0 : Φ ((ρ (ι z₀) - μ₁ • (1 : Module.End ℂ U)) ((ρ (ι z₀) - μ₂ • (1 : Module.End ℂ U)) u)) = 0 :=
      LinearMap.mem_ker.mp (hspan (hann u hu))
    have h1 : Φ ((ρ (ι z₀) - μ₁ • (1 : Module.End ℂ U)) ((ρ (ι z₀) - μ₂ • (1 : Module.End ℂ U)) u)) =
        (((ν z₀ : ℂ) - μ₁) * ((ν z₀ : ℂ) - μ₂)) • Φ u := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hz, smul_smul]
      module
    rw [h1] at h0
    exact (smul_eq_zero.mp h0).resolve_left (mul_ne_zero (sub_ne_zero.mpr hμ₁) (sub_ne_zero.mpr hμ₂))

  have hker₀ : U₀ ≤ LinearMap.ker ev := fun u hu => LinearMap.mem_ker.mpr (hkill ev hevM hevN u hu)
  have hkerM : ∀ (m : M) (u : U), u ∈ LinearMap.ker ev → ρ (ι m) u ∈ LinearMap.ker ev := fun m u hu => by
    rw [LinearMap.mem_ker] at hu ⊢
    rw [hevM, hu, map_zero, smul_zero]
  have hkerN : ∀ n ∈ N, ∀ u : U, u ∈ LinearMap.ker ev → ρ n u ∈ LinearMap.ker ev := fun n hn u hu => by
    rw [LinearMap.mem_ker] at hu ⊢
    rw [hevN n hn, hu]
  intro u hu
  rcases hirrQ (LinearMap.ker ev) hker₀ hkerM hkerN with hU₀ | htop
  ·
    have hu₀ : u ∈ U₀ := by
      rw [← hU₀]
      exact LinearMap.mem_ker.mpr hu
    refine hkill (ev ∘ₗ S) (fun m x => ?_) (fun n hn x => ?_) u hu₀
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hSρ, hevM]
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hSρ, hevN n hn]
  ·
    have hSu : S u ∈ LinearMap.ker ev := by
      rw [htop]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp hSu

private noncomputable def rightTranslationRep
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    LocalGL3 v →* Module.End ℂ ↥(principalSeries3 v χ) where
  toFun g := (gl3AmbientRightTranslate (R := ℂ) g).restrict fun _ hf => rightTranslate_mem_principalSeries3 hf g
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    show (f : LocalGL3 v → ℂ) (h * 1) = (f : LocalGL3 v → ℂ) h
    rw [mul_one]
  map_mul' g₁ g₂ := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    show (f : LocalGL3 v → ℂ) (h * (g₁ * g₂)) = (f : LocalGL3 v → ℂ) (h * g₁ * g₂)
    rw [mul_assoc]

private theorem rightTranslationRep_apply_coe (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)) :
    ((rightTranslationRep v χ g f : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) =
      gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 v → ℂ) := rfl

private theorem rightTranslationRep_mul_eq_mul_of_forall (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hT : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (T f)) (g : LocalGL3 v) :
    rightTranslationRep v χ g * T = T * rightTranslationRep v χ g := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact (hT g f).symm

private theorem forall_of_rightTranslationRep_mul_eq_mul (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hT : ∀ g : LocalGL3 v, rightTranslationRep v χ g * T = T * rightTranslationRep v χ g) (g : LocalGL3 v)
    (f : ↥(principalSeries3 v χ)) :
    (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
      gl3AmbientRightTranslate (R := ℂ) g (T f) :=
  (congrArg (fun u : ↥(principalSeries3 v χ) => (u : LocalGL3 v → ℂ)) (LinearMap.congr_fun (hT g) f)).symm

private theorem exists_eq_smul_id_of_linearEquiv {G : Type*} [Monoid G] {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (πV : G →* Module.End ℂ V) (πW : G →* Module.End ℂ W) (e : V ≃ₗ[ℂ] W) (c : G → ℂˣ)
    (he : ∀ (g : G) (x : V), e (πV g x) = (c g : ℂ) • πW g (e x))
    (hW : ∀ S : W →ₗ[ℂ] W, (∀ g : G, πW g * S = S * πW g) → ∃ a : ℂ, S = a • LinearMap.id)
    (T : V →ₗ[ℂ] V) (hT : ∀ g : G, πV g * T = T * πV g) : ∃ a : ℂ, T = a • LinearMap.id := by
  have hTapply : ∀ (g : G) (x : V), πV g (T x) = T (πV g x) := fun g x => LinearMap.congr_fun (hT g) x

  let S : W →ₗ[ℂ] W := (e : V →ₗ[ℂ] W) ∘ₗ T ∘ₗ (e.symm : W →ₗ[ℂ] V)
  have hSapply : ∀ x : V, S (e x) = e (T x) := by
    intro x
    simp [S]
  have hWg : ∀ (g : G) (x : V), πW g (e x) = ((c g)⁻¹ : ℂˣ) • e (πV g x) := by
    intro g x
    rw [he g x, Units.smul_def, smul_smul, Units.inv_mul, one_smul]
  have hS : ∀ g : G, πW g * S = S * πW g := by
    intro g
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    show πW g (S (e x)) = S (πW g (e x))
    rw [hSapply, hWg g x, Units.smul_def, map_smul, hSapply, ← hTapply, ← Units.smul_def]
    exact hWg g (T x)
  obtain ⟨a, ha⟩ := hW S hS
  refine ⟨a, LinearMap.ext fun x => ?_⟩
  have h₁ : S (e x) = a • e x := by rw [ha]; rfl
  rw [hSapply] at h₁
  apply e.injective
  rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul, h₁]

private theorem exists_eq_smul_id_of_principalSeries3_equiv (v : HeightOneSpectrum (𝓞 ℚ))
    (χ χ' : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (e : ↥(principalSeries3 v χ') ≃ₗ[ℂ] ↥(principalSeries3 v χ)) (c : LocalGL3 v → ℂˣ)
    (he : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ')),
      ((e ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ :
          ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) =
        (c g : ℂ) • gl3AmbientRightTranslate (R := ℂ) g (e f))
    (hχ : ∀ T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ),
      (∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
        (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
          gl3AmbientRightTranslate (R := ℂ) g (T f)) → ∃ a : ℂ, T = a • LinearMap.id)
    (T : ↥(principalSeries3 v χ') →ₗ[ℂ] ↥(principalSeries3 v χ'))
    (hT : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ')),
      (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (T f)) :
    ∃ a : ℂ, T = a • LinearMap.id :=
  exists_eq_smul_id_of_linearEquiv (rightTranslationRep v χ') (rightTranslationRep v χ) e c
    (fun g f => Subtype.ext (he g f))
    (fun S hS => hχ S (forall_of_rightTranslationRep_mul_eq_mul v χ S hS))
    T (rightTranslationRep_mul_eq_mul_of_forall v χ' T hT)

private noncomputable def functionModelRep {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (I : Submodule ℂ (G → W)) (hI : ∀ (g : G) (F : G → W), F ∈ I → (fun x => F (x * g)) ∈ I) :
    G →* Module.End ℂ ↥I where
  toFun g :=
    { toFun := fun F => ⟨fun x => (F : G → W) (x * g), hI g F F.2⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  map_one' := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    show (F : G → W) (x * 1) = (F : G → W) x
    rw [mul_one]
  map_mul' g₁ g₂ := by
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    show (F : G → W) (x * (g₁ * g₂)) = (F : G → W) (x * g₁ * g₂)
    rw [mul_assoc]

private theorem functionModelRep_mul_eq_mul_of_forall {G : Type*} [Group G] {W : Type*} [AddCommGroup W]
    [Module ℂ W] (I : Submodule ℂ (G → W)) (hI : ∀ (g : G) (F : G → W), F ∈ I → (fun x => F (x * g)) ∈ I)
    (T : ↥I →ₗ[ℂ] ↥I)
    (hT : ∀ (g : G) (F : ↥I), ((T ⟨fun x => (F : G → W) (x * g), hI g F F.2⟩ : ↥I) : G → W) =
      fun x => ((T F : ↥I) : G → W) (x * g)) (g : G) :
    functionModelRep I hI g * T = T * functionModelRep I hI g := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  exact (hT g F).symm

private theorem forall_of_functionModelRep_mul_eq_mul {G : Type*} [Group G] {W : Type*} [AddCommGroup W]
    [Module ℂ W] (I : Submodule ℂ (G → W)) (hI : ∀ (g : G) (F : G → W), F ∈ I → (fun x => F (x * g)) ∈ I)
    (T : ↥I →ₗ[ℂ] ↥I) (hT : ∀ g : G, functionModelRep I hI g * T = T * functionModelRep I hI g) (g : G)
    (F : ↥I) :
    ((T ⟨fun x => (F : G → W) (x * g), hI g F F.2⟩ : ↥I) : G → W) = fun x => ((T F : ↥I) : G → W) (x * g) :=
  (congrArg (fun u : ↥I => (u : G → W)) (LinearMap.congr_fun (hT g) F)).symm

section LeviKit

variable (v : HeightOneSpectrum (𝓞 ℚ))

private noncomputable def leviMat (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) : LocalGL3 v :=
  iotaGL m.1 * diagonal3 v ![1, 1, m.2]

private theorem leviMat_coe (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) :
    ((leviMat v m : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![(m.1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0,
          (m.1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1, 0;
        (m.1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0,
          (m.1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1, 0;
        0, 0, (m.2 : v.adicCompletion ℚ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMat, embedMat2, diagonal3, Matrix.mul_apply, Fin.sum_univ_three]

private noncomputable def leviEmbed3 : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ →* LocalGL3 v where
  toFun := leviMat v
  map_one' := by
    apply Units.ext
    rw [leviMat_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' m m' := by
    apply Units.ext
    rw [Units.val_mul, leviMat_coe, leviMat_coe, leviMat_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Prod.fst_mul, Prod.snd_mul, Units.val_mul]

private theorem leviEmbed3_apply (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) :
    leviEmbed3 v m = leviMat v m := rfl

private theorem leviEmbed3_entry_two_zero (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) :
    ((leviEmbed3 v m : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 := by
  rw [leviEmbed3_apply, leviMat_coe]; simp

private theorem leviEmbed3_entry_two_one (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) :
    ((leviEmbed3 v m : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 := by
  rw [leviEmbed3_apply, leviMat_coe]; simp

private theorem leviEmbed3_entry_two_two (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) :
    ((leviEmbed3 v m : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (m.2 : v.adicCompletion ℚ)
        := by
  rw [leviEmbed3_apply, leviMat_coe]; simp

private theorem leviEmbed3_entry_castSucc (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ)
    (i j : Fin 2) :
    ((leviEmbed3 v m : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
        = (m.1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j := by
  rw [leviEmbed3_apply, leviMat_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem leviEmbed3_one_mk (c : (v.adicCompletion ℚ)ˣ) : leviEmbed3 v (1, c) = diagonal3 v ![1, 1, c] := by
  show iotaGL (1 : GL (Fin 2) (v.adicCompletion ℚ)) * diagonal3 v ![1, 1, c] = diagonal3 v ![1, 1, c]
  rw [map_one, one_mul]

private theorem exists_leviEmbed3_mul_of_parabolic (p : LocalGL3 v)
    (h20 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0) (h21 : (p : Matrix (Fin 3) (Fin 3)
        (v.adicCompletion ℚ)) 2 1 = 0) :
    ∃ (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) (n : LocalGL3 v),
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = 1 ∧
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 = 1 ∧
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = 1 ∧
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 = 0 ∧
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧
      p = leviEmbed3 v m * n := by
  have hdetp : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det ≠ 0
      := ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit p)).ne_zero
  set B : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := !![(p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0,
      (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1; (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0,
      (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1] with hB
  have hdet3 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det = (p : Matrix (Fin 3) (Fin 3)
      (v.adicCompletion ℚ)) 2 2 * B.det := by
    rw [Matrix.det_fin_three, Matrix.det_fin_two, h20, h21, hB]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    ring
  have h22 : (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 ≠ 0 := left_ne_zero_of_mul (hdet3 ▸ hdetp)
  have hdetA : B.det ≠ 0 := right_ne_zero_of_mul (hdet3 ▸ hdetp)
  set A : GL (Fin 2) (v.adicCompletion ℚ) := Matrix.GeneralLinearGroup.mkOfDetNeZero B hdetA with hA
  have hAval : (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = B := rfl
  set c : (v.adicCompletion ℚ)ˣ := Units.mk0 _ h22 with hc

  have hinv : ((leviEmbed3 v (A, c))⁻¹ : LocalGL3 v) = leviEmbed3 v (A⁻¹, c⁻¹) := by rw [← map_inv]; rfl
  have hAA : ((A⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
      * (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e00 : ((A⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0
      * (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 + ((A⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))
      : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 * (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0
      = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hAval, hB] using congrFun (congrFun hAA 0) 0
  have e01 : ((A⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0
      * (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 + ((A⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))
      : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1 * (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1
      = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hAval, hB] using congrFun (congrFun hAA 0) 1
  have e10 : ((A⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0
      * (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 + ((A⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))
      : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 * (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0
      = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hAval, hB] using congrFun (congrFun hAA 1) 0
  have e11 : ((A⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0
      * (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 + ((A⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))
      : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1 * (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1
      = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hAval, hB] using congrFun (congrFun hAA 1) 1
  refine ⟨(A, c), (leviEmbed3 v (A, c))⁻¹ * p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (mul_inv_cancel_left _ _).symm⟩ <;>
    rw [hinv] <;> simp only [Units.val_mul, leviEmbed3_apply, leviMat_coe, Matrix.mul_apply, Fin.sum_univ_three]
  · simpa using e00
  · simpa using e11
  · simp [hc, h22]
  · simpa using e01
  · simpa using e10
  · simp [h20]
  · simp [h21]

private noncomputable def leviFactor (θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) : ℂˣ :=
  Units.mk0 ((((‖(m.1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2))
      / ‖(m.2 : v.adicCompletion ℚ)‖ : ℝ) : ℂ))
    (Complex.ofReal_ne_zero.mpr (div_ne_zero
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit m.1)).ne_zero) _).ne'
      (norm_ne_zero_iff.mpr m.2.ne_zero))) * θ' m.2

private theorem leviFactor_coe (θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) :
    ((leviFactor v θ' m : ℂˣ) : ℂ) =
      (((‖(m.1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2))
          / ‖(m.2 : v.adicCompletion ℚ)‖ : ℝ) : ℂ) * ((θ' m.2 : ℂˣ) : ℂ) := rfl

private theorem leviFactor_one_mk (θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : (v.adicCompletion ℚ)ˣ) :
    ((leviFactor v θ' (1, c) : ℂˣ) : ℂ) = ((θ' c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ) := by
  rw [leviFactor_coe]
  simp only [Units.val_one, Matrix.det_one, norm_one, Real.one_rpow, one_div]
  ring

private theorem eval_rightTranslate_leviEmbed3 (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂] (π₂ : GL (Fin 2) (v.adicCompletion ℚ) →* Module.End ℂ V₂)
    (Ψ : ↥(principalSeries3 v ![θ, θ, θ']) →ₗ[ℂ] V₂)
    (hlaw :
      ∀ (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ)
        (f : ↥(principalSeries3 v ![θ, θ, θ'])),
        (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
        (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 →
        (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ) →
        (∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
          = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) →
        Ψ ⟨gl3AmbientRightTranslate (R := ℂ) p f, rightTranslate_mem_principalSeries3 f.2 p⟩
          = ((((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2)) /
            ‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) • (((θ' c : ℂˣ) : ℂ) • π₂ A (Ψ f))))
    (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v ![θ, θ, θ'])) :
    Ψ ⟨gl3AmbientRightTranslate (R := ℂ) (leviEmbed3 v m) f, rightTranslate_mem_principalSeries3 f.2 (leviEmbed3 v m)⟩
      = ((leviFactor v θ' m : ℂˣ) : ℂ) • π₂ m.1 (Ψ f) := by
  have h := hlaw (leviEmbed3 v m) m.1 m.2 f (leviEmbed3_entry_two_zero v m) (leviEmbed3_entry_two_one v m)
    (leviEmbed3_entry_two_two v m) (leviEmbed3_entry_castSucc v m)
  rw [leviFactor_coe, ← smul_smul]
  exact h

private theorem eval_rightTranslate_radical (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂] (π₂ : GL (Fin 2) (v.adicCompletion ℚ) →* Module.End ℂ V₂)
    (Ψ : ↥(principalSeries3 v ![θ, θ, θ']) →ₗ[ℂ] V₂)
    (hlaw :
      ∀ (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ)
        (f : ↥(principalSeries3 v ![θ, θ, θ'])),
        (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
        (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 →
        (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ) →
        (∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
          = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) →
        Ψ ⟨gl3AmbientRightTranslate (R := ℂ) p f, rightTranslate_mem_principalSeries3 f.2 p⟩
          = ((((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2)) /
            ‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) • (((θ' c : ℂˣ) : ℂ) • π₂ A (Ψ f))))
    (n : LocalGL3 v)
    (h00 : (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = 1) (h11 : (n : Matrix (Fin 3) (Fin 3)
        (v.adicCompletion ℚ)) 1 1 = 1)
    (h22 : (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = 1) (h01 : (n : Matrix (Fin 3) (Fin 3)
        (v.adicCompletion ℚ)) 0 1 = 0)
    (h10 : (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0) (h20 : (n : Matrix (Fin 3) (Fin 3)
        (v.adicCompletion ℚ)) 2 0 = 0)
    (h21 : (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0) (f : ↥(principalSeries3 v ![θ, θ, θ'])) :
    Ψ ⟨gl3AmbientRightTranslate (R := ℂ) n f, rightTranslate_mem_principalSeries3 f.2 n⟩ = Ψ f := by
  have hblk : ∀ i j : Fin 2,
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j) = ((1 : GL (Fin 2)
          (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  have h := hlaw n 1 1 f h20 h21 (by rw [h22, Units.val_one]) hblk
  rw [h]
  simp only [Units.val_one, Matrix.det_one, norm_one, Real.one_rpow, div_one, Complex.ofReal_one, one_smul, map_one,
    Module.End.one_apply]

end LeviKit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

private theorem fixedVectors_comp_fst_prod_top {G N V : Type*} [Group G] [Group N] [AddCommGroup V] [Module ℂ V]
    (π : G →* Module.End ℂ V) (K : Subgroup G) :
    FLT.SmoothAdmissibleSchurCommutant.fixedVectors (π.comp (MonoidHom.fst G N)) (K.prod ⊤) =
      FLT.SmoothAdmissibleSchurCommutant.fixedVectors π K := by
  ext x
  rw [FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors, FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors]
  constructor
  · intro h u hu
    exact h (u, 1) (Subgroup.mem_prod.mpr ⟨hu, Subgroup.mem_top _⟩)
  · rintro h ⟨a, b⟩ hk
    exact h a (Subgroup.mem_prod.mp hk).1

private theorem mem_of_subtype_mem_map {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {p : Submodule R M}
    {q : Submodule R ↥p} {x : ↥p} (h : p.subtype x ∈ q.map p.subtype) : x ∈ q := by
  have h' := Submodule.mem_map.mp h
  obtain ⟨y, hy, hyx⟩ := h'
  have hxy : y = x := Subtype.ext hyx
  rw [← hxy]
  exact hy

private noncomputable def radicalSet (v : HeightOneSpectrum (𝓞 ℚ)) : Set (LocalGL3 v) :=
  {n | (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = 1 ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 = 1 ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = 1 ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 = 0 ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
    (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0}

private theorem mem_radicalSet_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : LocalGL3 v) :
    n ∈ radicalSet v ↔ (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = 1 ∧
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 = 1 ∧
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = 1 ∧
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 = 0 ∧
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
      (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 :=
  Iff.rfl

private theorem map_subtype_span_eq (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) :
    (Submodule.span ℂ {w : ↥(principalSeries3 v ![θ, θ, θ']) |
          ∃ n ∈ radicalSet v, ∃ u' : ↥(principalSeries3 v ![θ, θ, θ']),
            w = rightTranslationRep v ![θ, θ, θ'] n u' - u'}).map (principalSeries3 v ![θ, θ, θ']).subtype =
      Submodule.span ℂ {d : LocalGL3 v → ℂ | ∃ (n : LocalGL3 v) (f' : LocalGL3 v → ℂ),
        f' ∈ principalSeries3 v ![θ, θ, θ'] ∧
        (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = 1 ∧
        (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 = 1 ∧
        (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = 1 ∧
        (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 = 0 ∧
        (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧
        (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
        (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧
        d = gl3AmbientRightTranslate (R := ℂ) n f' - f'} := by
  rw [Submodule.map_span]
  congr 1
  ext d
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨n, hn, u', rfl⟩, rfl⟩
    have hn' := (mem_radicalSet_iff v n).mp hn
    obtain ⟨h00, h11, h22, h01, h10, h20, h21⟩ := hn'
    exact ⟨n, (u' : LocalGL3 v → ℂ), u'.2, h00, h11, h22, h01, h10, h20, h21, rfl⟩
  · rintro ⟨n, f', hf', h00, h11, h22, h01, h10, h20, h21, rfl⟩
    exact ⟨rightTranslationRep v ![θ, θ, θ'] n ⟨f', hf'⟩ - ⟨f', hf'⟩,
      ⟨n, (mem_radicalSet_iff v n).mpr ⟨h00, h11, h22, h01, h10, h20, h21⟩, ⟨f', hf'⟩, rfl⟩, rfl⟩

private theorem sq_sub_smul_mem_span_of_mem_ker
    (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    {V₂ : Type} [AddCommGroup V₂] [Module ℂ V₂] (Ψ : ↥(principalSeries3 v ![θ, θ, θ']) →ₗ[ℂ] V₂)
    (hker : ∀ f : ↥(principalSeries3 v ![θ, θ, θ']), Ψ f = 0 ↔
          ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
            (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → (f : LocalGL3 v → ℂ) p = 0)
    (hG1 : ∀ (c : (v.adicCompletion ℚ)ˣ) (f : LocalGL3 v → ℂ), f ∈ principalSeries3 v ![θ, θ, θ'] →
        (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) →
        ((gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) -
            (((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) •
              (1 : Module.End ℂ (LocalGL3 v → ℂ))) ^ 2) f ∈
          Submodule.span ℂ {d : LocalGL3 v → ℂ | ∃ (n : LocalGL3 v) (f' : LocalGL3 v → ℂ),
            f' ∈ principalSeries3 v ![θ, θ, θ'] ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = 1 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 = 1 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = 1 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 = 0 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧
            d = gl3AmbientRightTranslate (R := ℂ) n f' - f'})
    (c₀ : (v.adicCompletion ℚ)ˣ) (u : ↥(principalSeries3 v ![θ, θ, θ'])) (hu : u ∈ LinearMap.ker Ψ) :
    (rightTranslationRep v ![θ, θ, θ'] (diagonal3 v ![1, 1, c₀]) -
        (((θ c₀ : ℂˣ) : ℂ) * (((‖(c₀ : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) •
          (1 : Module.End ℂ ↥(principalSeries3 v ![θ, θ, θ'])))
      ((rightTranslationRep v ![θ, θ, θ'] (diagonal3 v ![1, 1, c₀]) -
        (((θ c₀ : ℂˣ) : ℂ) * (((‖(c₀ : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) •
          (1 : Module.End ℂ ↥(principalSeries3 v ![θ, θ, θ']))) u) ∈
      Submodule.span ℂ {w : ↥(principalSeries3 v ![θ, θ, θ']) |
          ∃ n ∈ radicalSet v, ∃ u' : ↥(principalSeries3 v ![θ, θ, θ']),
            w = rightTranslationRep v ![θ, θ, θ'] n u' - u'} := by
  have hvan : ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
      (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → (u : LocalGL3 v → ℂ) p = 0 :=
    (hker u).mp (LinearMap.mem_ker.mp hu)
  have h1 := hG1 c₀ u u.2 hvan

  have hcoe : (principalSeries3 v ![θ, θ, θ']).subtype
      ((rightTranslationRep v ![θ, θ, θ'] (diagonal3 v ![1, 1, c₀]) -
          (((θ c₀ : ℂˣ) : ℂ) * (((‖(c₀ : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) •
            (1 : Module.End ℂ ↥(principalSeries3 v ![θ, θ, θ'])))
        ((rightTranslationRep v ![θ, θ, θ'] (diagonal3 v ![1, 1, c₀]) -
          (((θ c₀ : ℂˣ) : ℂ) * (((‖(c₀ : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) •
            (1 : Module.End ℂ ↥(principalSeries3 v ![θ, θ, θ']))) u)) =
      ((gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c₀]) -
          (((θ c₀ : ℂˣ) : ℂ) * (((‖(c₀ : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) •
            (1 : Module.End ℂ (LocalGL3 v → ℂ))) ^ 2) (u : LocalGL3 v → ℂ) := by
    simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul, Submodule.coe_subtype, rightTranslationRep_apply_coe]
  have h2 : (principalSeries3 v ![θ, θ, θ']).subtype
      ((rightTranslationRep v ![θ, θ, θ'] (diagonal3 v ![1, 1, c₀]) -
          (((θ c₀ : ℂˣ) : ℂ) * (((‖(c₀ : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) •
            (1 : Module.End ℂ ↥(principalSeries3 v ![θ, θ, θ'])))
        ((rightTranslationRep v ![θ, θ, θ'] (diagonal3 v ![1, 1, c₀]) -
          (((θ c₀ : ℂˣ) : ℂ) * (((‖(c₀ : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) •
            (1 : Module.End ℂ ↥(principalSeries3 v ![θ, θ, θ']))) u)) ∈
      (Submodule.span ℂ {w : ↥(principalSeries3 v ![θ, θ, θ']) |
          ∃ n ∈ radicalSet v, ∃ u' : ↥(principalSeries3 v ![θ, θ, θ']),
            w = rightTranslationRep v ![θ, θ, θ'] n u' - u'}).map (principalSeries3 v ![θ, θ, θ']).subtype := by
    rw [map_subtype_span_eq, hcoe]
    exact h1
  exact mem_of_subtype_mem_map h2

private theorem eq_ker_or_eq_top_of_invariant
    (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    {V₂ : Type} [AddCommGroup V₂] [Module ℂ V₂] (Ψ : ↥(principalSeries3 v ![θ, θ, θ']) →ₗ[ℂ] V₂)
    (hker : ∀ f : ↥(principalSeries3 v ![θ, θ, θ']), Ψ f = 0 ↔
          ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
            (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → (f : LocalGL3 v → ℂ) p = 0)
    (hIP : ∀ U : Submodule ℂ (LocalGL3 v → ℂ), U ≤ principalSeries3 v ![θ, θ, θ'] →
        (∀ f ∈ principalSeries3 v ![θ, θ, θ'],
          (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
            (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) → f ∈ U) →
        (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 →
          U ≤ U.comap (gl3AmbientRightTranslate (R := ℂ) p)) →
        (∀ f ∈ U, ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) ∨
          U = principalSeries3 v ![θ, θ, θ'])
    (Y : Submodule ℂ ↥(principalSeries3 v ![θ, θ, θ'])) (hY : LinearMap.ker Ψ ≤ Y)
    (hM : ∀ (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) (u : ↥(principalSeries3 v ![θ, θ, θ'])),
      u ∈ Y → rightTranslationRep v ![θ, θ, θ'] (leviEmbed3 v m) u ∈ Y)
    (hN : ∀ n ∈ radicalSet v, ∀ u : ↥(principalSeries3 v ![θ, θ, θ']), u ∈ Y →
      rightTranslationRep v ![θ, θ, θ'] n u ∈ Y) :
    Y = LinearMap.ker Ψ ∨ Y = ⊤ := by
  have hvan : ∀ f ∈ principalSeries3 v ![θ, θ, θ'],
      (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
        (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) →
      f ∈ Y.map (principalSeries3 v ![θ, θ, θ']).subtype :=
    fun f hf hv => Submodule.mem_map_of_mem (hY (LinearMap.mem_ker.mpr ((hker ⟨f, hf⟩).mpr hv)))
  have hstab : ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
      (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 →
      Y.map (principalSeries3 v ![θ, θ, θ']).subtype ≤
        (Y.map (principalSeries3 v ![θ, θ, θ']).subtype).comap (gl3AmbientRightTranslate (R := ℂ) p) := by
    intro p hp0 hp1
    have hfac := exists_leviEmbed3_mul_of_parabolic v p hp0 hp1
    obtain ⟨m, n, h00, h11, h22, h01, h10, h20, h21, hp⟩ := hfac
    refine Submodule.map_le_iff_le_comap.mpr fun y hy => ?_
    rw [Submodule.mem_comap, Submodule.mem_comap]
    refine Submodule.mem_map.mpr
      ⟨rightTranslationRep v ![θ, θ, θ'] (leviEmbed3 v m) (rightTranslationRep v ![θ, θ, θ'] n y),
        hM m _ (hN n ((mem_radicalSet_iff v n).mpr ⟨h00, h11, h22, h01, h10, h20, h21⟩) y hy), ?_⟩
    rw [hp]
    funext x
    simp only [Submodule.coe_subtype, rightTranslationRep_apply_coe, gl3AmbientRightTranslate_apply, mul_assoc]
  have h := hIP (Y.map (principalSeries3 v ![θ, θ, θ']).subtype) (Submodule.map_subtype_le _ _) hvan hstab
  refine h.elim (fun h => Or.inl (le_antisymm ?_ hY)) (fun h => Or.inr ?_)
  · intro y hy
    exact LinearMap.mem_ker.mpr ((hker y).mpr (h _ (Submodule.mem_map_of_mem hy)))
  · exact Submodule.map_injective_of_injective (Submodule.injective_subtype _)
      (h.trans (Submodule.map_subtype_top _).symm)

private theorem exists_eq_smul_id_of_parabolicModel
    (v : HeightOneSpectrum (𝓞 ℚ)) (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hθ : ∃ c₀ : (v.adicCompletion ℚ)ˣ, θ c₀ ≠ θ' c₀)
    (χ₀ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ₀ : χ₀ = ![θ, θ, θ'])
    (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂]
    (π₂ : GL (Fin 2) (v.adicCompletion ℚ) →* Module.End ℂ V₂)
    (hI : FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep π₂)
    (hfix : ∃ (K₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) (u : V₂), u ≠ 0 ∧ (∀ k ∈ K₁, π₂ k u = u) ∧
      FiniteDimensional ℂ ↥(FLT.SmoothAdmissibleSchurCommutant.fixedVectors π₂ K₁))
    (hPσ : ∃ Ψ : ↥(principalSeries3 v χ₀) →ₗ[ℂ] V₂, Function.Surjective Ψ ∧
        (∀ f : ↥(principalSeries3 v χ₀), Ψ f = 0 ↔
          ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
            (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → (f : LocalGL3 v → ℂ) p = 0) ∧
        ∀ (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ)
          (f : ↥(principalSeries3 v χ₀)),
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ) →
          (∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
            = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) →
          Ψ ⟨gl3AmbientRightTranslate (R := ℂ) p f, rightTranslate_mem_principalSeries3 f.2 p⟩
            = ((((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2)) /
              ‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) • (((θ' c : ℂˣ) : ℂ) • π₂ A (Ψ f))))
    (hG1 : ∀ (c : (v.adicCompletion ℚ)ˣ) (f : LocalGL3 v → ℂ), f ∈ principalSeries3 v χ₀ →
        (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) →
        ((gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) -
            (((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) •
              (1 : Module.End ℂ (LocalGL3 v → ℂ))) ^ 2) f ∈
          Submodule.span ℂ {d : LocalGL3 v → ℂ | ∃ (n : LocalGL3 v) (f' : LocalGL3 v → ℂ),
            f' ∈ principalSeries3 v χ₀ ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = 1 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 = 1 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = 1 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 = 0 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧
            d = gl3AmbientRightTranslate (R := ℂ) n f' - f'})
    (hIP : ∀ U : Submodule ℂ (LocalGL3 v → ℂ), U ≤ principalSeries3 v χ₀ →
        (∀ f ∈ principalSeries3 v χ₀,
          (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
            (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) → f ∈ U) →
        (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 →
          U ≤ U.comap (gl3AmbientRightTranslate (R := ℂ) p)) →
        (∀ f ∈ U, ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) ∨
          U = principalSeries3 v χ₀)
    (T : ↥(principalSeries3 v χ₀) →ₗ[ℂ] ↥(principalSeries3 v χ₀))
    (hT : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ₀)),
      (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (T f)) :
    ∃ a : ℂ, T = a • LinearMap.id := by
  subst hχ₀
  obtain ⟨c₀, hc₀⟩ := hθ
  obtain ⟨Ψ, -, hker, hlaw⟩ := hPσ
  obtain ⟨K₁, w₀, hw₀, hw₀K, hfd⟩ := hfix
  obtain ⟨hI₀, hIW⟩ := hI

  have hlaw' : ∀ (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) (u : ↥(principalSeries3 v ![θ, θ, θ'])),
      Ψ (rightTranslationRep v ![θ, θ, θ'] (leviEmbed3 v m) u) =
        (leviFactor v θ' m : ℂ) •
          (π₂.comp (MonoidHom.fst (GL (Fin 2) (v.adicCompletion ℚ)) (v.adicCompletion ℚ)ˣ)) m (Ψ u) :=
    fun m u => by
      show Ψ _ = _ • π₂ m.1 (Ψ u)
      exact eval_rightTranslate_leviEmbed3 v θ θ' V₂ π₂ Ψ hlaw m u
  have hevN : ∀ n ∈ radicalSet v, ∀ u : ↥(principalSeries3 v ![θ, θ, θ']),
      Ψ (rightTranslationRep v ![θ, θ, θ'] n u) = Ψ u := by
    intro n hn u
    have hn' := (mem_radicalSet_iff v n).mp hn
    obtain ⟨h00, h11, h22, h01, h10, h20, h21⟩ := hn'
    exact eval_rightTranslate_radical v θ θ' V₂ π₂ Ψ hlaw n h00 h11 h22 h01 h10 h20 h21 u

  have hdet : ∀ u : ↥(principalSeries3 v ![θ, θ, θ']),
      (∀ g : LocalGL3 v, Ψ (rightTranslationRep v ![θ, θ, θ'] g u) = 0) → u = 0 := by
    intro u hu
    apply Subtype.ext
    funext g
    have h1 := (hker _).mp (hu g) 1 (by rw [Units.val_one, Matrix.one_apply_ne (by decide)])
      (by rw [Units.val_one, Matrix.one_apply_ne (by decide)])
    rw [rightTranslationRep_apply_coe, gl3AmbientRightTranslate_apply, one_mul] at h1
    rw [Submodule.coe_zero, Pi.zero_apply]
    exact h1

  have hirr : FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep
      (π₂.comp (MonoidHom.fst (GL (Fin 2) (v.adicCompletion ℚ)) (v.adicCompletion ℚ)ˣ)) :=
    ⟨hI₀, fun W hW => hIW W fun A x hx => hW (A, 1) x hx⟩
  have hw₀K' : ∀ k ∈ K₁.prod (⊤ : Subgroup (v.adicCompletion ℚ)ˣ),
      (π₂.comp (MonoidHom.fst (GL (Fin 2) (v.adicCompletion ℚ)) (v.adicCompletion ℚ)ˣ)) k w₀ = w₀ :=
    fun k hk => hw₀K k.1 (Subgroup.mem_prod.mp hk).1
  have hfd' : FiniteDimensional ℂ ↥(FLT.SmoothAdmissibleSchurCommutant.fixedVectors
      (π₂.comp (MonoidHom.fst (GL (Fin 2) (v.adicCompletion ℚ)) (v.adicCompletion ℚ)ˣ))
      (K₁.prod (⊤ : Subgroup (v.adicCompletion ℚ)ˣ))) := by
    rw [fixedVectors_comp_fst_prod_top]
    exact hfd

  have hz₀ :
      (π₂.comp (MonoidHom.fst (GL (Fin 2) (v.adicCompletion ℚ)) (v.adicCompletion ℚ)ˣ))
        ((1 : GL (Fin 2) (v.adicCompletion ℚ)), c₀) = 1 := by
    show π₂ 1 = 1
    exact map_one π₂
  obtain ⟨μ, hμ⟩ : ∃ μ : ℂ, μ = ((θ c₀ : ℂˣ) : ℂ) * (((‖(c₀ : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ) := ⟨_, rfl⟩
  have hν : ((leviFactor v θ' ((1 : GL (Fin 2) (v.adicCompletion ℚ)), c₀) : ℂˣ) : ℂ) ≠ μ := by
    rw [leviFactor_one_mk, hμ]
    intro h
    have hr : (((‖(c₀ : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr c₀.ne_zero))
    exact hc₀ (Units.ext (mul_right_cancel₀ hr h)).symm

  have hann : ∀ u ∈ LinearMap.ker Ψ,
      (rightTranslationRep v ![θ, θ, θ'] (leviEmbed3 v ((1 : GL (Fin 2) (v.adicCompletion ℚ)), c₀)) -
          μ • (1 : Module.End ℂ ↥(principalSeries3 v ![θ, θ, θ'])))
        ((rightTranslationRep v ![θ, θ, θ'] (leviEmbed3 v ((1 : GL (Fin 2) (v.adicCompletion ℚ)), c₀)) -
          μ • (1 : Module.End ℂ ↥(principalSeries3 v ![θ, θ, θ']))) u) ∈
        Submodule.span ℂ {w : ↥(principalSeries3 v ![θ, θ, θ']) |
          ∃ n ∈ radicalSet v, ∃ u' : ↥(principalSeries3 v ![θ, θ, θ']),
            w = rightTranslationRep v ![θ, θ, θ'] n u' - u'} := by
    intro u hu
    rw [leviEmbed3_one_mk, hμ]
    exact sq_sub_smul_mem_span_of_mem_ker v θ θ' Ψ hker hG1 c₀ u hu
  have hirrQ : ∀ Y : Submodule ℂ ↥(principalSeries3 v ![θ, θ, θ']), LinearMap.ker Ψ ≤ Y →
      (∀ (m : GL (Fin 2) (v.adicCompletion ℚ) × (v.adicCompletion ℚ)ˣ) (u : ↥(principalSeries3 v ![θ, θ, θ'])),
        u ∈ Y → rightTranslationRep v ![θ, θ, θ'] (leviEmbed3 v m) u ∈ Y) →
      (∀ n ∈ radicalSet v, ∀ u : ↥(principalSeries3 v ![θ, θ, θ']), u ∈ Y →
        rightTranslationRep v ![θ, θ, θ'] n u ∈ Y) →
      Y = LinearMap.ker Ψ ∨ Y = ⊤ :=
    fun Y hY hM hN => eq_ker_or_eq_top_of_invariant v θ θ' Ψ hker hIP Y hY hM hN

  have hcore := exists_eq_smul_one_of_eval_law (rightTranslationRep v ![θ, θ, θ'])
    (π₂.comp (MonoidHom.fst (GL (Fin 2) (v.adicCompletion ℚ)) (v.adicCompletion ℚ)ˣ))
    (leviEmbed3 v) (leviFactor v θ') Ψ hlaw' hdet hirr hw₀ hw₀K' hfd'
    (fun S hS => eval_kernel_stable_of_quadratic_annihilator (rightTranslationRep v ![θ, θ, θ'])
      (π₂.comp (MonoidHom.fst (GL (Fin 2) (v.adicCompletion ℚ)) (v.adicCompletion ℚ)ˣ)) (leviEmbed3 v)
      (leviFactor v θ') (radicalSet v) Ψ hlaw' hevN ((1 : GL (Fin 2) (v.adicCompletion ℚ)), c₀) hz₀ μ μ hν hν
      (LinearMap.ker Ψ) hann hirrQ S hS)
    T (rightTranslationRep_mul_eq_mul_of_forall v ![θ, θ, θ'] T hT)
  obtain ⟨a, ha⟩ := hcore
  rw [Module.End.one_eq_id] at ha
  exact ⟨a, ha⟩

end LanglandsTunnell.CubicInduction.ScalarCommutant
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective.LanglandsTunnell.CubicInduction.PadicTransport"

private theorem exists_eq_smul_id_of_leviData
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hunit : ∀ i, ∀ x : (v.adicCompletion ℚ)ˣ, ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (htwo : ¬ Function.Injective χ) (hne : ¬ (χ 0 = χ 1 ∧ χ 1 = χ 2))
    (T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hT : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (T f))
    (θ θ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : χ = ![θ, θ, θ'] ∨ χ = ![θ, θ', θ] ∨ χ = ![θ', θ, θ])
    (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂]
    (π₂ : GL (Fin 2) (v.adicCompletion ℚ) →* Module.End ℂ V₂)
    (hI : FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep π₂)
    (hfix : ∃ (K₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) (u : V₂), u ≠ 0 ∧ (∀ k ∈ K₁, π₂ k u = u) ∧
      FiniteDimensional ℂ ↥(FLT.SmoothAdmissibleSchurCommutant.fixedVectors π₂ K₁))
    (hPσ : ∃ Ψ : ↥(principalSeries3 v ![θ, θ, θ']) →ₗ[ℂ] V₂, Function.Surjective Ψ ∧
        (∀ f : ↥(principalSeries3 v ![θ, θ, θ']), Ψ f = 0 ↔
          ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
            (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → (f : LocalGL3 v → ℂ) p = 0) ∧
        ∀ (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ)
          (f : ↥(principalSeries3 v ![θ, θ, θ'])),
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ) →
          (∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
            = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) →
          Ψ ⟨gl3AmbientRightTranslate (R := ℂ) p f, rightTranslate_mem_principalSeries3 f.2 p⟩
            = ((((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2)) /
              ‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) • (((θ' c : ℂˣ) : ℂ) • π₂ A (Ψ f))))
    (hG : ∀ w : Equiv.Perm (Fin 3), ∃ Φ : ↥(principalSeries3 v χ) ≃ₗ[ℂ] ↥(principalSeries3 v (χ ∘ ⇑w)),
        ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
          (Φ ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ)
            = gl3AmbientRightTranslate (R := ℂ) g (Φ f))
    (hG1 : ∀ (c : (v.adicCompletion ℚ)ˣ) (f : LocalGL3 v → ℂ), f ∈ principalSeries3 v ![θ, θ, θ'] →
        (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) →
        ((gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, 1, c]) -
            (((θ c : ℂˣ) : ℂ) * (((‖(c : v.adicCompletion ℚ)‖⁻¹ : ℝ)) : ℂ)) •
              (1 : Module.End ℂ (LocalGL3 v → ℂ))) ^ 2) f ∈
          Submodule.span ℂ {d : LocalGL3 v → ℂ | ∃ (n : LocalGL3 v) (f' : LocalGL3 v → ℂ),
            f' ∈ principalSeries3 v ![θ, θ, θ'] ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 0 = 1 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 = 1 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = 1 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 = 0 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 ∧
            (n : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 ∧
            d = gl3AmbientRightTranslate (R := ℂ) n f' - f'})
    (hIP : ∀ U : Submodule ℂ (LocalGL3 v → ℂ), U ≤ principalSeries3 v ![θ, θ, θ'] →
        (∀ f ∈ principalSeries3 v ![θ, θ, θ'],
          (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
            (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) → f ∈ U) →
        (∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 →
          U ≤ U.comap (gl3AmbientRightTranslate (R := ℂ) p)) →
        (∀ f ∈ U, ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
          (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → f p = 0) ∨
          U = principalSeries3 v ![θ, θ, θ']) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  have _ := hunit
  have _ := htwo

  have hθ : ∃ c₀ : (v.adicCompletion ℚ)ˣ, θ c₀ ≠ θ' c₀ := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have hθθ : θ' = θ := (MonoidHom.ext h).symm
    have hχ' : χ = ![θ, θ, θ] := by
      rcases hχ with hc | hc | hc <;> rw [hc, hθθ]
    apply hne
    rw [hχ']
    exact ⟨rfl, rfl⟩

  obtain ⟨w, hw⟩ : ∃ w : Equiv.Perm (Fin 3), χ ∘ ⇑w = ![θ, θ, θ'] := by
    rcases hχ with hc | hc | hc
    · refine ⟨1, ?_⟩
      rw [hc, Equiv.Perm.coe_one, Function.comp_id]
    · refine ⟨Equiv.swap 1 2, ?_⟩
      rw [hc]
      exact funext fun i => by fin_cases i <;> rfl
    · refine ⟨Equiv.swap 0 2, ?_⟩
      rw [hc]
      exact funext fun i => by fin_cases i <;> rfl
  have hGw := hG w
  obtain ⟨Φ, hΦ⟩ := hGw

  have main : ∀ χ₀ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ), χ₀ = ![θ, θ, θ'] →
      ∀ Φ : ↥(principalSeries3 v χ) ≃ₗ[ℂ] ↥(principalSeries3 v χ₀),
        (∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
          (Φ ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ)
            = gl3AmbientRightTranslate (R := ℂ) g (Φ f)) →
        ∃ c : ℂ, T = c • LinearMap.id := by
    intro χ₀ hχ₀ Φ hΦ
    subst hχ₀
    exact ScalarCommutant.exists_eq_smul_id_of_principalSeries3_equiv v ![θ, θ, θ'] χ Φ 1
      (fun g f => by rw [hΦ g f, Pi.one_apply, Units.val_one, one_smul])
      (fun S hS => ScalarCommutant.exists_eq_smul_id_of_parabolicModel v θ θ' hθ ![θ, θ, θ'] rfl V₂ π₂ hI hfix hPσ
        hG1 hIP S hS)
      T hT
  exact main (χ ∘ ⇑w) hw Φ hΦ

private theorem exists_pair_of_not_injective {α : Type*} (χ : Fin 3 → α) (h : ¬ Function.Injective χ) :
    ∃ θ θ' : α, χ = ![θ, θ, θ'] ∨ χ = ![θ, θ', θ] ∨ χ = ![θ', θ, θ] := by
  by_cases h01 : χ 0 = χ 1
  · exact ⟨χ 0, χ 2, Or.inl (funext fun k => by fin_cases k <;> simp [h01])⟩
  by_cases h02 : χ 0 = χ 2
  · exact ⟨χ 0, χ 1, Or.inr (Or.inl (funext fun k => by fin_cases k <;> simp [h02]))⟩
  by_cases h12 : χ 1 = χ 2
  · exact ⟨χ 1, χ 0, Or.inr (Or.inr (funext fun k => by fin_cases k <;> simp [h12]))⟩
  refine absurd (fun a b hab => ?_) h
  fin_cases a <;> fin_cases b <;> simp at hab ⊢
  · exact h01 hab
  · exact h02 hab
  · exact h01 hab.symm
  · exact h12 hab
  · exact h02 hab.symm
  · exact h12 hab.symm

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hunit : ∀ i, ∀ x : (v.adicCompletion ℚ)ˣ, ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (htwo : ¬ Function.Injective χ) (hne : ¬ (χ 0 = χ 1 ∧ χ 1 = χ 2))
    (T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hT : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (T f)) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  have hunif : ∀ (χ' : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (f : LocalGL3 v → ℂ), f ∈ principalSeries3 v χ' →
        ∃ n : ℕ, ∀ k : LocalGL3 v,
          (∀ i j : Fin 3,
            Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
              ≤ WithZero.exp (-(n : ℤ))) →
          gl3AmbientRightTranslate (R := ℂ) k f = f := fun χ' f hf =>
    exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ' f hf
  classical
  by_cases hzero : ∀ f : ↥(principalSeries3 v χ), f = 0
  · refine ⟨0, LinearMap.ext fun f => ?_⟩
    rw [LinearMap.smul_apply, zero_smul]
    exact hzero _
  obtain ⟨f, hf⟩ := not_forall.mp hzero
  have hf0 : (f : LocalGL3 v → ℂ) ≠ 0 := fun h => hf (Submodule.coe_eq_zero.mp h)
  have hlcχ : ∀ i, IsLocallyConstant (χ i) := fun i =>
    LanglandsTunnell.CubicInduction.isLocallyConstant_of_mem_principalSeries3_of_ne_zero v χ f i f.2 hf0
  obtain ⟨θ, θ', hχ⟩ := exists_pair_of_not_injective χ htwo
  have hlc : ∀ i, IsLocallyConstant (![θ, θ, θ'] i) := by
    rcases hχ with h | h | h <;> rw [h] at hlcχ
    · exact hlcχ
    · intro i
      fin_cases i
      · simpa using hlcχ 0
      · simpa using hlcχ 0
      · simpa using hlcχ 1
    · intro i
      fin_cases i
      · simpa using hlcχ 1
      · simpa using hlcχ 1
      · simpa using hlcχ 0
  suffices key : ∀ (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂]
          (π₂ : GL (Fin 2) (v.adicCompletion ℚ) →* Module.End ℂ V₂),
          FLT.SmoothAdmissibleSchurCommutant.IsIrreducibleRep π₂ →
          (∃ (K₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) (u : V₂), u ≠ 0 ∧ (∀ k ∈ K₁, π₂ k u = u) ∧
          FiniteDimensional ℂ ↥(FLT.SmoothAdmissibleSchurCommutant.fixedVectors π₂ K₁)) →
          (∃ Ψ : ↥(principalSeries3 v ![θ, θ, θ']) →ₗ[ℂ] V₂, Function.Surjective Ψ ∧
            (∀ f : ↥(principalSeries3 v ![θ, θ, θ']), Ψ f = 0 ↔
              ∀ p : LocalGL3 v, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
                (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → (f : LocalGL3 v → ℂ) p = 0) ∧
            ∀ (p : LocalGL3 v) (A : GL (Fin 2) (v.adicCompletion ℚ)) (c : (v.adicCompletion ℚ)ˣ)
              (f : ↥(principalSeries3 v ![θ, θ, θ'])),
              (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
              (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 →
              (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = (c : v.adicCompletion ℚ) →
              (∀ i j : Fin 2, (p : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (Fin.castSucc i) (Fin.castSucc j)
                = (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) →
              Ψ ⟨gl3AmbientRightTranslate (R := ℂ) p f, rightTranslate_mem_principalSeries3 f.2 p⟩
                = ((((‖(A : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det‖ ^ ((1 : ℝ) / 2)) /
                  ‖(c : v.adicCompletion ℚ)‖ : ℝ) : ℂ) • (((θ' c : ℂˣ) : ℂ) • π₂ A (Ψ f)))) →
      ∃ c : ℂ, T = c • LinearMap.id by
    exact key _ (principalSeries2Rep (v := v) ![θ, θ])
      (LanglandsTunnell.CubicInduction.PadicTransport.isIrreducibleRep_principalSeries2Rep_pair v θ θ' hlc)
      (LanglandsTunnell.CubicInduction.CellSectionAdmissibility.exists_fixed_ne_zero_and_finiteDimensional_fixedVectors
        v θ θ' hlc)
      (LanglandsTunnell.CubicInduction.LeviRestriction.exists_surjective_leviRestriction_principalSeries3 v θ θ'
        hlc)
  intro V₂ _ _ π₂ hI hfix hPσ
  exact exists_eq_smul_id_of_leviData v χ hunit htwo hne T hT θ θ' hχ V₂ π₂ hI hfix hPσ
    (LanglandsTunnell.CubicInduction.PrincipalSeriesPermutation.permutationDatum v χ hunit hlcχ)
    (LanglandsTunnell.CubicInduction.ParabolicCharts.annihilator_sq_mem_span_radicalDifferences v θ θ'
      fun f hf => hunif _ f hf)
    (LanglandsTunnell.CubicInduction.principalSeries3_vanishOnParabolic_or_eq_of_isIrreducibleRep v θ θ' V₂ π₂
      hI hPσ)

end S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective (solution)
