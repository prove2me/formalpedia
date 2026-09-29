-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/06369424-db60-58e4-8bab-b03902ef30b7

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_MeasureTheory_ContractionDecay
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open Matrix

noncomputable section

namespace SiegelGram

variable {L : Type*} [Field L]

private def gramMatrix3 (A : Matrix (Fin 3) (Fin 3) L) : Matrix (Fin 3) (Fin 3) L := A * Aᵀ

private def gramZeta (A : Matrix (Fin 3) (Fin 3) L) : L := gramMatrix3 A 0 2 / gramMatrix3 A 2 2

private theorem gramMatrix3_apply (A : Matrix (Fin 3) (Fin 3) L) (i j : Fin 3) :
    gramMatrix3 A i j = A i 0 * A j 0 + A i 1 * A j 1 + A i 2 * A j 2 := by
  simp [gramMatrix3, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gramZeta_def (A : Matrix (Fin 3) (Fin 3) L) :
    gramZeta A = (A 0 0 * A 2 0 + A 0 1 * A 2 1 + A 0 2 * A 2 2) /
      (A 2 0 * A 2 0 + A 2 1 * A 2 1 + A 2 2 * A 2 2) := by
  simp only [gramZeta, gramMatrix3_apply]

private theorem gramMatrix3_mul_of_transpose_mul_eq_one (A k : Matrix (Fin 3) (Fin 3) L) (hk : kᵀ * k = 1) :
    gramMatrix3 (A * k) = gramMatrix3 A := by
  have hk' : k * kᵀ = 1 := _root_.mul_eq_one_comm.mp hk
  simp only [gramMatrix3, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc k, hk', Matrix.one_mul]

private theorem gramZeta_mul_of_transpose_mul_eq_one (A k : Matrix (Fin 3) (Fin 3) L) (hk : kᵀ * k = 1) :
    gramZeta (A * k) = gramZeta A := by
  simp only [gramZeta, gramMatrix3_mul_of_transpose_mul_eq_one A k hk]

private theorem gramZeta_smul (c : L) (hc : c ≠ 0) (A : Matrix (Fin 3) (Fin 3) L)
    (hA : A 2 0 * A 2 0 + A 2 1 * A 2 1 + A 2 2 * A 2 2 ≠ 0) :
    gramZeta (c • A) = gramZeta A := by
  rw [gramZeta_def, gramZeta_def]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hc2 : c * c ≠ 0 := mul_ne_zero hc hc
  rw [div_eq_div_iff (by intro h; apply mul_ne_zero hc2 hA; linear_combination h) hA]
  ring

private theorem gramZeta_diagonal_mul (d : Fin 3 → L) (h2 : d 2 ≠ 0) (A : Matrix (Fin 3) (Fin 3) L)
    (hA : A 2 0 * A 2 0 + A 2 1 * A 2 1 + A 2 2 * A 2 2 ≠ 0) :
    gramZeta (Matrix.diagonal d * A) = d 0 / d 2 * gramZeta A := by
  rw [gramZeta_def, gramZeta_def]
  simp only [Matrix.diagonal_mul]
  have hden : d 2 * A 2 0 * (d 2 * A 2 0) + d 2 * A 2 1 * (d 2 * A 2 1) + d 2 * A 2 2 * (d 2 * A 2 2) ≠ 0 := by
    have h : d 2 * A 2 0 * (d 2 * A 2 0) + d 2 * A 2 1 * (d 2 * A 2 1) + d 2 * A 2 2 * (d 2 * A 2 2) =
        d 2 * d 2 * (A 2 0 * A 2 0 + A 2 1 * A 2 1 + A 2 2 * A 2 2) := by ring
    rw [h]
    exact mul_ne_zero (mul_ne_zero h2 h2) hA
  rw [div_mul_div_comm, div_eq_div_iff hden (mul_ne_zero h2 hA)]
  ring

private theorem gramZeta_upperUnipotent_mul_diagonal_mul (x y z : L) (d : Fin 3 → L) (hd : d 2 ≠ 0)
    (k : Matrix (Fin 3) (Fin 3) L) (hk : kᵀ * k = 1) :
    gramZeta (!![(1 : L), x, z; 0, 1, y; 0, 0, 1] * Matrix.diagonal d * k) = z := by
  rw [gramZeta_mul_of_transpose_mul_eq_one _ k hk, gramZeta_def]
  simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.tail_cons, one_mul, zero_mul, mul_zero, zero_add, add_zero]
  field_simp

private theorem gramZeta_shear_mul (s : L) (A : Matrix (Fin 3) (Fin 3) L)
    (hA : A 2 0 * A 2 0 + A 2 1 * A 2 1 + A 2 2 * A 2 2 ≠ 0) :
    gramZeta (!![(1 : L), 0, s; 0, 1, 0; 0, 0, 1] * A) = gramZeta A + s := by
  rw [gramZeta_def, gramZeta_def]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.tail_cons, one_mul, zero_mul, zero_add, add_zero]
  rw [div_add' _ _ _ hA, div_eq_div_iff hA hA]
  ring

private theorem gramZeta_mul_diagonal_of_last_row (N : Matrix (Fin 3) (Fin 3) L) (h20 : N 2 0 = 0) (h21 : N 2 1 = 0)
    (h22 : N 2 2 = 1) (d : Fin 3 → L) (hd : d 2 ≠ 0) :
    gramZeta (N * Matrix.diagonal d) = N 0 2 := by
  rw [gramZeta_def]
  simp only [Matrix.mul_diagonal, h20, h21, h22, zero_mul, mul_zero, zero_add, one_mul]
  rw [div_eq_iff (mul_ne_zero hd hd)]
  ring

private theorem eq_diagonal_of_offDiag_eq_zero (M : Matrix (Fin 3) (Fin 3) L) (hM : ∀ i j : Fin 3, i ≠ j → M i j = 0) :
    M = Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ h, hM i j h]

private theorem coe_inv_of_coe_eq_diagonal (u : GL (Fin 3) L) (e : Fin 3 → L) (he : ∀ i, e i ≠ 0)
    (hu : (u : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal e) :
    ((u⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal (fun i => (e i)⁻¹) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [hu, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (he i)

private theorem mul_apply_two_of_last_row (N M : Matrix (Fin 3) (Fin 3) L) (h20 : N 2 0 = 0) (h21 : N 2 1 = 0)
    (h22 : N 2 2 = 1) (j : Fin 3) : (N * M) 2 j = M 2 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, h20, h21, h22]

end SiegelGram

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂ archPlaceComponent3 AdelicGL globalPointsGL upperUnipotent3 upperUnipotent3_coe localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN componentAt3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open SiegelGram

section SizeLaws

variable {L : Type*} [NormedField L]

private theorem lastRowEucl_upperUnipotent3_mul (x y z : L) (g : GL (Fin 3) L) :
    lastRowEucl (upperUnipotent3 x y z * g) = lastRowEucl g := by
  simp [lastRowEucl, Matrix.mul_apply, Fin.sum_univ_three]

private theorem bottomMinor_upperUnipotent3_mul (x y z : L) (g : GL (Fin 3) L) (j j' : Fin 3) :
    bottomMinor (upperUnipotent3 x y z * g) j j' = bottomMinor g j j' := by
  simp only [bottomMinor, Units.val_mul, upperUnipotent3_coe, Matrix.mul_apply, Fin.sum_univ_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.tail_cons]
  ring

private theorem minorEucl_upperUnipotent3_mul (x y z : L) (g : GL (Fin 3) L) :
    minorEucl (upperUnipotent3 x y z * g) = minorEucl g := by
  simp only [minorEucl, bottomMinor_upperUnipotent3_mul]

private theorem detSize_upperUnipotent3_mul (x y z : L) (g : GL (Fin 3) L) :
    detSize (upperUnipotent3 x y z * g) = detSize g := by
  have hdet : ((upperUnipotent3 x y z : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = 1 := by
    rw [upperUnipotent3_coe, Matrix.det_fin_three]
    simp
  simp only [detSize, Units.val_mul, Matrix.det_mul, hdet, one_mul]

private theorem lastRowEucl_of_coe_eq_diagonal (t : GL (Fin 3) L) (d : Fin 3 → L)
    (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal d) :
    lastRowEucl t = ‖d 2‖ := by
  simp only [lastRowEucl, ht, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (show (2 : Fin 3) ≠ 0 by decide),
    Matrix.diagonal_apply_ne _ (show (2 : Fin 3) ≠ 1 by decide), norm_zero]
  rw [show (0 : ℝ) ^ 2 + 0 ^ 2 + ‖d 2‖ ^ 2 = ‖d 2‖ ^ 2 by ring]
  exact Real.sqrt_sq (norm_nonneg _)

private theorem minorEucl_of_coe_eq_diagonal (t : GL (Fin 3) L) (d : Fin 3 → L)
    (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal d) :
    minorEucl t = ‖d 1 * d 2‖ := by
  simp only [minorEucl, bottomMinor, ht, Matrix.diagonal_apply]
  simp only [show ((1 : Fin 3) = 0) = False by decide, show ((1 : Fin 3) = 2) = False by decide,
    show ((2 : Fin 3) = 0) = False by decide, show ((2 : Fin 3) = 1) = False by decide, if_false, if_true,
    mul_zero, zero_mul, sub_zero, norm_zero]
  rw [show (0 : ℝ) ^ 2 + 0 ^ 2 + ‖d 1 * d 2‖ ^ 2 = ‖d 1 * d 2‖ ^ 2 by ring]
  exact Real.sqrt_sq (norm_nonneg _)

private theorem detSize_of_coe_eq_diagonal (t : GL (Fin 3) L) (d : Fin 3 → L)
    (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal d) :
    detSize t = ‖d 0 * d 1 * d 2‖ := by
  simp only [detSize, ht, Matrix.det_diagonal, Fin.prod_univ_three]

private theorem rootSizes_of_coe_eq_diagonal (t : GL (Fin 3) L) (d : Fin 3 → L)
    (ht : (t : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal d) (h1 : d 1 ≠ 0) (h2 : d 2 ≠ 0) :
    detSize t * lastRowEucl t / minorEucl t ^ 2 = ‖d 0‖ / ‖d 1‖ ∧
      minorEucl t / lastRowEucl t ^ 2 = ‖d 1‖ / ‖d 2‖ := by
  rw [detSize_of_coe_eq_diagonal t d ht, lastRowEucl_of_coe_eq_diagonal t d ht, minorEucl_of_coe_eq_diagonal t d ht]
  have n1 : ‖d 1‖ ≠ 0 := norm_ne_zero_iff.mpr h1
  have n2 : ‖d 2‖ ≠ 0 := norm_ne_zero_iff.mpr h2
  simp only [norm_mul]
  constructor
  · field_simp
  · field_simp

private theorem lastRowEucl_diag_mul (p g : GL (Fin 3) L) (a b c : L)
    (hp : (p : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![a, b, c]) :
    lastRowEucl (p * g) = ‖c‖ * lastRowEucl g := by
  simp only [lastRowEucl, Units.val_mul, hp, Matrix.diagonal_mul]
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, norm_mul, mul_pow]
  rw [show ‖c‖ ^ 2 * ‖(g : Matrix (Fin 3) (Fin 3) L) 2 0‖ ^ 2 + ‖c‖ ^ 2 * ‖(g : Matrix (Fin 3) (Fin 3) L) 2 1‖ ^ 2 +
      ‖c‖ ^ 2 * ‖(g : Matrix (Fin 3) (Fin 3) L) 2 2‖ ^ 2 = ‖c‖ ^ 2 * (‖(g : Matrix (Fin 3) (Fin 3) L) 2 0‖ ^ 2 +
      ‖(g : Matrix (Fin 3) (Fin 3) L) 2 1‖ ^ 2 + ‖(g : Matrix (Fin 3) (Fin 3) L) 2 2‖ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

private theorem bottomMinor_diag_mul (p g : GL (Fin 3) L) (a b c : L)
    (hp : (p : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![a, b, c]) (j j' : Fin 3) :
    bottomMinor (p * g) j j' = (b * c) * bottomMinor g j j' := by
  simp only [bottomMinor, Units.val_mul, hp, Matrix.diagonal_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem minorEucl_diag_mul (p g : GL (Fin 3) L) (a b c : L)
    (hp : (p : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![a, b, c]) :
    minorEucl (p * g) = ‖b * c‖ * minorEucl g := by
  simp only [minorEucl, bottomMinor_diag_mul p g a b c hp, norm_mul, mul_pow]
  rw [show ‖b‖ ^ 2 * ‖c‖ ^ 2 * ‖bottomMinor g 0 1‖ ^ 2 + ‖b‖ ^ 2 * ‖c‖ ^ 2 * ‖bottomMinor g 0 2‖ ^ 2 +
        ‖b‖ ^ 2 * ‖c‖ ^ 2 * ‖bottomMinor g 1 2‖ ^ 2 =
      (‖b‖ * ‖c‖) ^ 2 * (‖bottomMinor g 0 1‖ ^ 2 + ‖bottomMinor g 0 2‖ ^ 2 + ‖bottomMinor g 1 2‖ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

private theorem detSize_diag_mul (p g : GL (Fin 3) L) (a b c : L)
    (hp : (p : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![a, b, c]) :
    detSize (p * g) = ‖a * b * c‖ * detSize g := by
  simp only [detSize, Units.val_mul, Matrix.det_mul, hp, Matrix.det_diagonal, Fin.prod_univ_three, norm_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

private theorem rootSizes_diag_mul (p g : GL (Fin 3) L) (a b c : L) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hp : (p : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![a, b, c])
    (hl : lastRowEucl g ≠ 0) (hm : minorEucl g ≠ 0) :
    detSize (p * g) * lastRowEucl (p * g) / minorEucl (p * g) ^ 2 =
        ‖a‖ / ‖b‖ * (detSize g * lastRowEucl g / minorEucl g ^ 2) ∧
      minorEucl (p * g) / lastRowEucl (p * g) ^ 2 = ‖b‖ / ‖c‖ * (minorEucl g / lastRowEucl g ^ 2) := by
  rw [detSize_diag_mul p g a b c hp, lastRowEucl_diag_mul p g a b c hp, minorEucl_diag_mul p g a b c hp]
  have na : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have nb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have nc : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  simp only [norm_mul]
  constructor
  · field_simp
  · field_simp

private theorem rootSizes_contraction_one (p g : GL (Fin 3) L) (a b : L) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : (p : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![a, b, b])
    (hl : lastRowEucl g ≠ 0) (hm : minorEucl g ≠ 0) :
    detSize (p * g) * lastRowEucl (p * g) / minorEucl (p * g) ^ 2 =
        ‖a‖ / ‖b‖ * (detSize g * lastRowEucl g / minorEucl g ^ 2) ∧
      minorEucl (p * g) / lastRowEucl (p * g) ^ 2 = minorEucl g / lastRowEucl g ^ 2 := by
  obtain ⟨h1, h2⟩ := rootSizes_diag_mul p g a b b ha hb hb hp hl hm
  refine ⟨h1, ?_⟩
  rw [h2, div_self (norm_ne_zero_iff.mpr hb), one_mul]

private theorem rootSizes_contraction_two (p g : GL (Fin 3) L) (a c : L) (ha : a ≠ 0) (hc : c ≠ 0)
    (hp : (p : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![a, a, c])
    (hl : lastRowEucl g ≠ 0) (hm : minorEucl g ≠ 0) :
    detSize (p * g) * lastRowEucl (p * g) / minorEucl (p * g) ^ 2 =
        detSize g * lastRowEucl g / minorEucl g ^ 2 ∧
      minorEucl (p * g) / lastRowEucl (p * g) ^ 2 = ‖a‖ / ‖c‖ * (minorEucl g / lastRowEucl g ^ 2) := by
  obtain ⟨h1, h2⟩ := rootSizes_diag_mul p g a a c ha ha hc hp hl hm
  refine ⟨?_, h2⟩
  rw [h1, div_self (norm_ne_zero_iff.mpr ha), one_mul]

end SizeLaws

section RealOrthogonal

private theorem sq_lastRowEucl_eq_gram (g : GL (Fin 3) ℝ) :
    lastRowEucl g ^ 2 = gramMatrix3 (g : Matrix (Fin 3) (Fin 3) ℝ) 2 2 := by
  rw [lastRowEucl, Real.sq_sqrt (by positivity), gramMatrix3_apply]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

private theorem sq_minorEucl_eq_gram (g : GL (Fin 3) ℝ) :
    minorEucl g ^ 2 = gramMatrix3 (g : Matrix (Fin 3) (Fin 3) ℝ) 1 1 * gramMatrix3 (g : Matrix (Fin 3) (Fin 3) ℝ) 2 2 -
      gramMatrix3 (g : Matrix (Fin 3) (Fin 3) ℝ) 1 2 ^ 2 := by
  rw [minorEucl, Real.sq_sqrt (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs, bottomMinor, gramMatrix3_apply]
  ring

private theorem lastRowEucl_mul_of_transpose_mul_eq_one (g k : GL (Fin 3) ℝ)
    (hk : (k : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (k : Matrix (Fin 3) (Fin 3) ℝ) = 1) :
    lastRowEucl (g * k) = lastRowEucl g := by
  have h := sq_lastRowEucl_eq_gram (g * k)
  rw [Units.val_mul, gramMatrix3_mul_of_transpose_mul_eq_one _ _ hk, ← sq_lastRowEucl_eq_gram g] at h
  have h1 : 0 ≤ lastRowEucl (g * k) := by unfold lastRowEucl; positivity
  have h2 : 0 ≤ lastRowEucl g := by unfold lastRowEucl; positivity
  exact le_antisymm (by nlinarith [h, h1, h2]) (by nlinarith [h, h1, h2])

private theorem minorEucl_mul_of_transpose_mul_eq_one (g k : GL (Fin 3) ℝ)
    (hk : (k : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (k : Matrix (Fin 3) (Fin 3) ℝ) = 1) :
    minorEucl (g * k) = minorEucl g := by
  have h := sq_minorEucl_eq_gram (g * k)
  rw [Units.val_mul, gramMatrix3_mul_of_transpose_mul_eq_one _ _ hk, ← sq_minorEucl_eq_gram g] at h
  have h1 : 0 ≤ minorEucl (g * k) := by unfold minorEucl; positivity
  have h2 : 0 ≤ minorEucl g := by unfold minorEucl; positivity
  exact le_antisymm (by nlinarith [h, h1, h2]) (by nlinarith [h, h1, h2])

private theorem detSize_mul_of_transpose_mul_eq_one (g k : GL (Fin 3) ℝ)
    (hk : (k : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (k : Matrix (Fin 3) (Fin 3) ℝ) = 1) :
    detSize (g * k) = detSize g := by
  have hdet : |(k : Matrix (Fin 3) (Fin 3) ℝ).det| = 1 := by
    have h1 := congrArg Matrix.det hk
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    have h2 : |(k : Matrix (Fin 3) (Fin 3) ℝ).det| ^ 2 = 1 := by rw [sq_abs, sq, h1]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).mp h2
  simp only [detSize, Units.val_mul, Matrix.det_mul, Real.norm_eq_abs, abs_mul, hdet, mul_one]

private theorem rootSizes_device_stage_one (p g : GL (Fin 3) ℝ)
    (hp : (p : Matrix (Fin 3) (Fin 3) ℝ) = Matrix.diagonal ![1 / 4, 2, 2])
    (hl : lastRowEucl g ≠ 0) (hm : minorEucl g ≠ 0) :
    detSize (p * g) * lastRowEucl (p * g) / minorEucl (p * g) ^ 2 =
        (detSize g * lastRowEucl g / minorEucl g ^ 2) / 8 ∧
      minorEucl (p * g) / lastRowEucl (p * g) ^ 2 = minorEucl g / lastRowEucl g ^ 2 := by
  obtain ⟨h1, h2⟩ := rootSizes_contraction_one p g (1 / 4 : ℝ) 2 (by norm_num) (by norm_num) hp hl hm
  refine ⟨?_, h2⟩
  rw [h1, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring

private theorem rootSizes_device_stage_two (p g : GL (Fin 3) ℝ)
    (hp : (p : Matrix (Fin 3) (Fin 3) ℝ) = Matrix.diagonal ![1 / 2, 1 / 2, 4])
    (hl : lastRowEucl g ≠ 0) (hm : minorEucl g ≠ 0) :
    detSize (p * g) * lastRowEucl (p * g) / minorEucl (p * g) ^ 2 =
        detSize g * lastRowEucl g / minorEucl g ^ 2 ∧
      minorEucl (p * g) / lastRowEucl (p * g) ^ 2 = (minorEucl g / lastRowEucl g ^ 2) / 8 := by
  obtain ⟨h1, h2⟩ := rootSizes_contraction_two p g (1 / 2 : ℝ) 4 (by norm_num) (by norm_num) hp hl hm
  refine ⟨h1, ?_⟩
  rw [h2, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  ring

private theorem det_device_stage_one : (Matrix.diagonal ![(1 / 4 : ℝ), 2, 2]).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  norm_num

private theorem det_device_stage_two : (Matrix.diagonal ![(1 / 2 : ℝ), 1 / 2, 4]).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  norm_num

private theorem gramZeta_device_stage_one (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A 2 0 * A 2 0 + A 2 1 * A 2 1 + A 2 2 * A 2 2 ≠ 0) :
    gramZeta (Matrix.diagonal ![1 / 4, 2, 2] * A) = gramZeta A / 8 := by
  rw [gramZeta_diagonal_mul _ (by simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; norm_num) A hA]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

private theorem gramZeta_device_stage_two (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A 2 0 * A 2 0 + A 2 1 * A 2 1 + A 2 2 * A 2 2 ≠ 0) :
    gramZeta (Matrix.diagonal ![1 / 2, 1 / 2, 4] * A) = gramZeta A / 8 := by
  rw [gramZeta_diagonal_mul _ (by simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; norm_num) A hA]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

end RealOrthogonal

end LanglandsTunnell.CubicInduction

end

set_option autoImplicit false

open Matrix

noncomputable section

namespace SiegelGram

section Field

variable {L : Type*} [Field L]

private def shear3 (s : L) : Matrix (Fin 3) (Fin 3) L := !![1, 0, s; 0, 1, 0; 0, 0, 1]

private theorem shear3_mul_apply_zero (s : L) (M : Matrix (Fin 3) (Fin 3) L) (j : Fin 3) :
    (shear3 s * M) 0 j = M 0 j + s * M 2 j := by
  simp [shear3, Matrix.mul_apply, Fin.sum_univ_three]

private theorem shear3_mul_apply_one (s : L) (M : Matrix (Fin 3) (Fin 3) L) (j : Fin 3) :
    (shear3 s * M) 1 j = M 1 j := by
  simp [shear3, Matrix.mul_apply, Fin.sum_univ_three]

private theorem shear3_mul_apply_two (s : L) (M : Matrix (Fin 3) (Fin 3) L) (j : Fin 3) :
    (shear3 s * M) 2 j = M 2 j := by
  simp [shear3, Matrix.mul_apply, Fin.sum_univ_three]

private theorem det_shear3 (s : L) : (shear3 s).det = 1 := by
  rw [shear3, Matrix.det_fin_three]
  simp

private theorem diagonal_mul_mul_diagonal_inv_apply (d : Fin 3 → L) (N : Matrix (Fin 3) (Fin 3) L) (i j : Fin 3) :
    (Matrix.diagonal d * N * Matrix.diagonal (fun i => (d i)⁻¹)) i j = d i * N i j * (d j)⁻¹ := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem shear3_mul_diagonal_mul_eq (d : Fin 3 → L) (hd : ∀ i, d i ≠ 0) (s : L)
    (N T K : Matrix (Fin 3) (Fin 3) L) :
    shear3 s * Matrix.diagonal d * (N * T * K) =
      shear3 s * (Matrix.diagonal d * N * Matrix.diagonal (fun i => (d i)⁻¹)) * (Matrix.diagonal d * T) * K := by
  have h : Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d = (1 : Matrix (Fin 3) (Fin 3) L) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hd i)
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal fun i => (d i)⁻¹), h, Matrix.one_mul]

private theorem unipotent_conj_shear (d : Fin 3 → L) (hd : ∀ i, d i ≠ 0) (s : L) (N : Matrix (Fin 3) (Fin 3) L)
    (h1 : ∀ i, N i i = 1) (h0 : ∀ i j : Fin 3, j < i → N i j = 0) :
    let N' := shear3 s * (Matrix.diagonal d * N * Matrix.diagonal (fun i => (d i)⁻¹))
    (∀ i, N' i i = 1) ∧ (∀ i j : Fin 3, j < i → N' i j = 0) ∧
      N' 0 1 = d 0 / d 1 * N 0 1 ∧ N' 1 2 = d 1 / d 2 * N 1 2 ∧ N' 0 2 = d 0 / d 2 * N 0 2 + s := by
  intro N'
  have h20 : N 2 0 = 0 := h0 2 0 (by decide)
  have h21 : N 2 1 = 0 := h0 2 1 (by decide)
  have h10 : N 1 0 = 0 := h0 1 0 (by decide)
  have e0 : ∀ j, N' 0 j = d 0 * N 0 j * (d j)⁻¹ + s * (d 2 * N 2 j * (d j)⁻¹) := fun j => by
    simp only [N', shear3_mul_apply_zero, diagonal_mul_mul_diagonal_inv_apply]
  have e1 : ∀ j, N' 1 j = d 1 * N 1 j * (d j)⁻¹ := fun j => by
    simp only [N', shear3_mul_apply_one, diagonal_mul_mul_diagonal_inv_apply]
  have e2 : ∀ j, N' 2 j = d 2 * N 2 j * (d j)⁻¹ := fun j => by
    simp only [N', shear3_mul_apply_two, diagonal_mul_mul_diagonal_inv_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simp only [Fin.zero_eta, e0, h1, h20, mul_one, mul_zero, zero_mul, add_zero]
      exact mul_inv_cancel₀ (hd 0)
    · simp only [Fin.mk_one, e1, h1, mul_one]
      exact mul_inv_cancel₀ (hd 1)
    · simp only [Fin.reduceFinMk, e2, h1, mul_one]
      exact mul_inv_cancel₀ (hd 2)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · simp only [Fin.mk_one, Fin.zero_eta, e1, h10, mul_zero, zero_mul]
    · simp only [Fin.reduceFinMk, Fin.zero_eta, e2, h20, mul_zero, zero_mul]
    · simp only [Fin.reduceFinMk, Fin.mk_one, e2, h21, mul_zero, zero_mul]
  · rw [e0, h21]
    ring
  · rw [e1]
    field_simp
  · rw [e0, h1, mul_one, mul_inv_cancel₀ (hd 2), mul_one]
    ring

end Field

section Normed

variable {L : Type*} [NormedField L]

private theorem box_conj_shear (d : Fin 3 → L) (hd : ∀ i, d i ≠ 0) (s : L) (C : ℝ) (hC : 1 ≤ C)
    (r01 : ‖d 0 / d 1‖ ≤ 1) (r12 : ‖d 1 / d 2‖ ≤ 1) (r02 : ‖d 0 / d 2‖ * C + ‖s‖ ≤ C)
    (N : Matrix (Fin 3) (Fin 3) L) (h1 : ∀ i, N i i = 1) (h0 : ∀ i j : Fin 3, j < i → N i j = 0)
    (hbox : ∀ i j, ‖N i j‖ ≤ C) :
    ∀ i j, ‖(shear3 s * (Matrix.diagonal d * N * Matrix.diagonal (fun i => (d i)⁻¹))) i j‖ ≤ C := by
  obtain ⟨u1, u0, u01, u12, u02⟩ := unipotent_conj_shear d hd s N h1 h0
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  intro i j
  rcases lt_trichotomy j i with hji | rfl | hij
  · rw [u0 i j hji, norm_zero]
    exact hC0
  · rw [u1, norm_one]
    exact hC
  · fin_cases i <;> fin_cases j <;> simp at hij
    · simp only [Fin.zero_eta, Fin.mk_one, u01, norm_mul]
      calc ‖d 0 / d 1‖ * ‖N 0 1‖ ≤ 1 * C := mul_le_mul r01 (hbox 0 1) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
    · simp only [Fin.zero_eta, Fin.reduceFinMk, u02]
      calc ‖d 0 / d 2 * N 0 2 + s‖ ≤ ‖d 0 / d 2 * N 0 2‖ + ‖s‖ := norm_add_le _ _
        _ = ‖d 0 / d 2‖ * ‖N 0 2‖ + ‖s‖ := by rw [norm_mul]
        _ ≤ ‖d 0 / d 2‖ * C + ‖s‖ :=
            add_le_add (mul_le_mul_of_nonneg_left (hbox 0 2) (norm_nonneg _)) le_rfl
        _ ≤ C := r02
    · simp only [Fin.mk_one, Fin.reduceFinMk, u12, norm_mul]
      calc ‖d 1 / d 2‖ * ‖N 1 2‖ ≤ 1 * C := mul_le_mul r12 (hbox 1 2) (norm_nonneg _) zero_le_one
        _ = C := one_mul C

end Normed

section Device

private theorem device_ratios_stage_one (C : ℝ) (hC : 0 ≤ C) (s : ℝ) (hs : ‖s‖ = C / 2) :
    ‖(![(1 / 4 : ℝ), 2, 2] 0) / (![(1 / 4 : ℝ), 2, 2] 1)‖ ≤ 1 ∧
      ‖(![(1 / 4 : ℝ), 2, 2] 1) / (![(1 / 4 : ℝ), 2, 2] 2)‖ ≤ 1 ∧
      ‖(![(1 / 4 : ℝ), 2, 2] 0) / (![(1 / 4 : ℝ), 2, 2] 2)‖ * C + ‖s‖ ≤ C := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Real.norm_eq_abs, hs]
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_pos (by norm_num)]
    norm_num
  · rw [abs_of_pos (by norm_num)]
    norm_num
  · rw [abs_of_pos (by norm_num)]
    linarith

private theorem device_ratios_stage_two (C : ℝ) (hC : 0 ≤ C) (s : ℝ) (hs : ‖s‖ = C / 2) :
    ‖(![(1 / 2 : ℝ), 1 / 2, 4] 0) / (![(1 / 2 : ℝ), 1 / 2, 4] 1)‖ ≤ 1 ∧
      ‖(![(1 / 2 : ℝ), 1 / 2, 4] 1) / (![(1 / 2 : ℝ), 1 / 2, 4] 2)‖ ≤ 1 ∧
      ‖(![(1 / 2 : ℝ), 1 / 2, 4] 0) / (![(1 / 2 : ℝ), 1 / 2, 4] 2)‖ * C + ‖s‖ ≤ C := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Real.norm_eq_abs, hs]
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_of_pos (by norm_num)]
    norm_num
  · rw [abs_of_pos (by norm_num)]
    norm_num
  · rw [abs_of_pos (by norm_num)]
    linarith

end Device

end SiegelGram

end

set_option autoImplicit false

namespace SiegelGram

private theorem le_max_one_of_pow_three_le {x M : ℝ} (_hx : 0 ≤ x) (h : x ^ 3 ≤ M) : x ≤ max 1 M := by
  by_cases h1 : x ≤ 1
  · exact h1.trans (le_max_left _ _)
  · have h1' : 1 < x := not_le.mp h1
    refine le_trans ?_ (le_max_right _ _)
    calc x = x * 1 * 1 := by ring
      _ ≤ x * x * x := by gcongr
      _ = x ^ 3 := by ring
      _ ≤ M := h

private theorem last_size_le {x₀ x₁ x₂ c β : ℝ} (hc : 0 < c) (h2 : 0 ≤ x₂)
    (r₁ : c * x₁ ≤ x₀) (r₂ : c * x₂ ≤ x₁) (hβ : x₀ * x₁ * x₂ ≤ β) :
    x₂ ≤ max 1 (β / c ^ 3) := by
  have h1 : 0 ≤ x₁ := le_trans (by positivity) r₂
  have h0 : 0 ≤ x₀ := le_trans (by positivity) r₁
  apply le_max_one_of_pow_three_le h2
  rw [le_div_iff₀ (by positivity)]
  have hx₀ : c * (c * x₂) ≤ x₀ := le_trans (by gcongr) r₁
  calc x₂ ^ 3 * c ^ 3 = (c * (c * x₂)) * (c * x₂) * x₂ := by ring
    _ ≤ x₀ * x₁ * x₂ := by gcongr
    _ ≤ β := hβ

private theorem slice_sizes_le {x₀ x₁ x₂ c K β : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (h2 : 0 ≤ x₂)
    (r₁ : c * x₁ ≤ x₀) (r₂ : c * x₂ ≤ x₁) (u₁ : x₀ ≤ K * x₁) (u₂ : x₁ ≤ K * x₂) (hβ : x₀ * x₁ * x₂ ≤ β) :
    x₂ ≤ max 1 (β / c ^ 3) ∧ x₁ ≤ K * max 1 (β / c ^ 3) ∧ x₀ ≤ K ^ 2 * max 1 (β / c ^ 3) := by
  have hx₂ := last_size_le hc h2 r₁ r₂ hβ
  have hx₁ : x₁ ≤ K * max 1 (β / c ^ 3) := u₂.trans (by gcongr)
  refine ⟨hx₂, hx₁, ?_⟩
  calc x₀ ≤ K * x₁ := u₁
    _ ≤ K * (K * max 1 (β / c ^ 3)) := by gcongr
    _ = K ^ 2 * max 1 (β / c ^ 3) := by ring

private theorem slice_sizes_pos {x₀ x₁ x₂ α : ℝ} (hα : 0 < α) (h0 : 0 ≤ x₀) (h1 : 0 ≤ x₁) (h2 : 0 ≤ x₂)
    (hαle : α ≤ x₀ * x₁ * x₂) : 0 < x₀ ∧ 0 < x₁ ∧ 0 < x₂ := by
  have hprod : 0 < x₀ * x₁ * x₂ := hα.trans_le hαle
  refine ⟨?_, ?_, ?_⟩
  · rcases h0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hprod
      simp at hprod
  · rcases h1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hprod
      simp at hprod
  · rcases h2.lt_or_eq with h | h
    · exact h
    · rw [← h] at hprod
      simp at hprod

private theorem slice_sizes_ge {x₀ x₁ x₂ c K α β : ℝ} (hc : 0 < c) (hK : 0 < K) (_hα : 0 < α)
    (h0 : 0 ≤ x₀) (h1 : 0 ≤ x₁) (h2 : 0 ≤ x₂)
    (r₁ : c * x₁ ≤ x₀) (r₂ : c * x₂ ≤ x₁) (u₁ : x₀ ≤ K * x₁) (u₂ : x₁ ≤ K * x₂)
    (hαle : α ≤ x₀ * x₁ * x₂) (hβ : x₀ * x₁ * x₂ ≤ β) :
    α / (K ^ 2 * max 1 (β / c ^ 3) * (K * max 1 (β / c ^ 3))) ≤ x₂ ∧
      α / (K ^ 2 * max 1 (β / c ^ 3) * max 1 (β / c ^ 3)) ≤ x₁ ∧
      α / (K * max 1 (β / c ^ 3) * max 1 (β / c ^ 3)) ≤ x₀ := by
  obtain ⟨b₂, b₁, b₀⟩ := slice_sizes_le hc hK.le h2 r₁ r₂ u₁ u₂ hβ
  have hU : 0 < max 1 (β / c ^ 3) := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    calc α ≤ x₀ * x₁ * x₂ := hαle
      _ ≤ K ^ 2 * max 1 (β / c ^ 3) * (K * max 1 (β / c ^ 3)) * x₂ := by gcongr
      _ = x₂ * (K ^ 2 * max 1 (β / c ^ 3) * (K * max 1 (β / c ^ 3))) := by ring
  · rw [div_le_iff₀ (by positivity)]
    calc α ≤ x₀ * x₁ * x₂ := hαle
      _ = x₀ * x₂ * x₁ := by ring
      _ ≤ K ^ 2 * max 1 (β / c ^ 3) * max 1 (β / c ^ 3) * x₁ := by gcongr
      _ = x₁ * (K ^ 2 * max 1 (β / c ^ 3) * max 1 (β / c ^ 3)) := by ring
  · rw [div_le_iff₀ (by positivity)]
    calc α ≤ x₀ * x₁ * x₂ := hαle
      _ = x₁ * x₂ * x₀ := by ring
      _ ≤ K * max 1 (β / c ^ 3) * max 1 (β / c ^ 3) * x₀ := by gcongr
      _ = x₀ * (K * max 1 (β / c ^ 3) * max 1 (β / c ^ 3)) := by ring

end SiegelGram

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField Matrix LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.LanglandsTunnell.CubicInduction"

noncomputable section

namespace SiegelContraction

open SiegelGram

private def IsWitness (c C : ℝ) (n t k : AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
  (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
  (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
  (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
  ∀ w : InfinitePlace ℚ,
    (∀ i j : Fin 3,
      (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
      (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
      ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
    (∀ i j : Fin 3, i ≠ j →
      (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
    c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
    (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
        (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1

private def siegelSet (c C : ℝ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {g | ∃ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, g = n * t * k ∧ IsWitness c C n t k}

section Device

variable (w₀ : InfinitePlace ℚ)

private def devDiag (a b c' : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c' ≠ 0) : GL (Fin 3) w₀.Completion :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal ![algebraMap ℚ w₀.Completion a, algebraMap ℚ w₀.Completion b, algebraMap ℚ w₀.Completion c'])
    (by
      rw [Matrix.det_diagonal, Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      exact mul_ne_zero (mul_ne_zero ((map_ne_zero _).2 ha) ((map_ne_zero _).2 hb)) ((map_ne_zero _).2 hc))

private theorem devDiag_coe (a b c' : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c' ≠ 0) :
    ((devDiag w₀ a b c' ha hb hc : GL (Fin 3) w₀.Completion) : Matrix (Fin 3) (Fin 3) w₀.Completion) =
      Matrix.diagonal ![algebraMap ℚ w₀.Completion a, algebraMap ℚ w₀.Completion b, algebraMap ℚ w₀.Completion c'] :=
  rfl

private theorem devDiag_entries_ne_zero (a b c' : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c' ≠ 0) (i : Fin 3) :
    (![algebraMap ℚ w₀.Completion a, algebraMap ℚ w₀.Completion b, algebraMap ℚ w₀.Completion c'] :
      Fin 3 → w₀.Completion) i ≠ 0 := by
  fin_cases i
  · exact (map_ne_zero _).2 ha
  · exact (map_ne_zero _).2 hb
  · exact (map_ne_zero _).2 hc

variable (ι : GL (Fin 3) w₀.Completion →* AdelicGL 3 (𝓞 ℚ) ℚ) (A : AdelicGL 3 (𝓞 ℚ) ℚ →* GL (Fin 3) w₀.Completion)
  (hw : ∀ w : InfinitePlace ℚ, w = w₀)
  (hι_fin : ∀ (u : GL (Fin 3) w₀.Completion) (p : HeightOneSpectrum (𝓞 ℚ)), componentAt3 (𝓞 ℚ) ℚ p (ι u) = 1)
  (hAι : ∀ u : GL (Fin 3) w₀.Completion, A (ι u) = u)
  (hA : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, archPlaceComponent3 ℚ w₀ g = A g)
  (hρ : ∀ q : ℚ, ‖algebraMap ℚ w₀.Completion q‖ = |q|)

private theorem device_mul_eq (P D n t k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    P * (n * t * k) = (P * n * D⁻¹) * (D * t) * k := by
  simp only [mul_assoc, inv_mul_cancel_left]

private theorem diag_entries_ne_zero (T : GL (Fin 3) w₀.Completion) (d : Fin 3 → w₀.Completion)
    (hT : (T : Matrix (Fin 3) (Fin 3) w₀.Completion) = Matrix.diagonal d) (i : Fin 3) : d i ≠ 0 := by
  intro hi
  have hdet : (T : Matrix (Fin 3) (Fin 3) w₀.Completion).det ≠ 0 := (Matrix.GeneralLinearGroup.det T).ne_zero
  rw [hT, Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hdet
  exact hdet i (Finset.mem_univ i) hi

include hw hι_fin hAι hA hρ in

private theorem witness_contract (a b c' : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c' ≠ 0) (s : ℚ) {c C : ℝ}
    (r01 : |a / b| ≤ 1) (r12 : |b / c'| ≤ 1) (r02 : |a / c'| * C + |s| ≤ C)
    {n t k : AdelicGL 3 (𝓞 ℚ) ℚ} (hW : IsWitness c C n t k)
    (hr₁ : c ≤ |a / b| * archRoot₁ ℚ w₀ t) (hr₂ : c ≤ |b / c'| * archRoot₂ ℚ w₀ t) :
    let D := ι (devDiag w₀ a b c' ha hb hc)
    let P := ι (upperUnipotent3 0 0 (algebraMap ℚ w₀.Completion s) * devDiag w₀ a b c' ha hb hc)
    IsWitness c C (P * n * D⁻¹) (D * t) k ∧
      archRoot₁ ℚ w₀ (D * t) = |a / b| * archRoot₁ ℚ w₀ t ∧
      archRoot₂ ℚ w₀ (D * t) = |b / c'| * archRoot₂ ℚ w₀ t := by
  intro D P
  obtain ⟨hn_fin, ht_fin, hk_fin, harch⟩ := hW
  obtain ⟨hn_box, ht_off, hroot₁, hroot₂, hk_orth⟩ := harch w₀
  rw [hA] at hn_box ht_off
  set e : Fin 3 → w₀.Completion :=
    ![algebraMap ℚ w₀.Completion a, algebraMap ℚ w₀.Completion b, algebraMap ℚ w₀.Completion c'] with he_def
  have he : ∀ i, e i ≠ 0 := devDiag_entries_ne_zero w₀ a b c' ha hb hc
  set d : Fin 3 → w₀.Completion := fun i => (A t : Matrix (Fin 3) (Fin 3) w₀.Completion) i i with hd_def
  have hT : (A t : Matrix (Fin 3) (Fin 3) w₀.Completion) = Matrix.diagonal d :=
    eq_diagonal_of_offDiag_eq_zero _ ht_off
  have hdne : ∀ i, d i ≠ 0 := diag_entries_ne_zero w₀ (A t) d hT
  have hratio : ∀ x y : ℚ, y ≠ 0 → ‖algebraMap ℚ w₀.Completion x / algebraMap ℚ w₀.Completion y‖ = |x / y| := by
    intro x y _
    rw [← map_div₀, hρ]
  have hC1 : (1 : ℝ) ≤ C := by
    have h := (hn_box 0 0).2.2
    rwa [(hn_box 0 0).1, norm_one] at h
  have hADt : A (D * t) = devDiag w₀ a b c' ha hb hc * A t := by
    rw [map_mul, hAι]
  have hADt_coe : ((A (D * t) : GL (Fin 3) w₀.Completion) : Matrix (Fin 3) (Fin 3) w₀.Completion) =
      Matrix.diagonal (fun i => e i * d i) := by
    rw [hADt, Units.val_mul, devDiag_coe, hT, Matrix.diagonal_mul_diagonal]
  have hAn' : ((A (P * n * D⁻¹) : GL (Fin 3) w₀.Completion) : Matrix (Fin 3) (Fin 3) w₀.Completion) =
      shear3 (algebraMap ℚ w₀.Completion s) *
        (Matrix.diagonal e * (A n : Matrix (Fin 3) (Fin 3) w₀.Completion) * Matrix.diagonal (fun i => (e i)⁻¹)) := by
    rw [map_mul, map_mul, map_inv, hAι, hAι, Units.val_mul, Units.val_mul, Units.val_mul, upperUnipotent3_coe,
      devDiag_coe, coe_inv_of_coe_eq_diagonal _ e he (devDiag_coe w₀ a b c' ha hb hc)]
    simp only [shear3, Matrix.mul_assoc, he_def]
  obtain ⟨hu1, hu0, -, -, -⟩ := unipotent_conj_shear e he (algebraMap ℚ w₀.Completion s)
    (A n : Matrix (Fin 3) (Fin 3) w₀.Completion) (fun i => (hn_box i i).1) (fun i j hij => (hn_box i j).2.1 hij)
  have hvec : e 0 = algebraMap ℚ w₀.Completion a ∧ e 1 = algebraMap ℚ w₀.Completion b ∧
      e 2 = algebraMap ℚ w₀.Completion c' := ⟨rfl, rfl, rfl⟩
  have hn01 : ‖e 0 / e 1‖ = ((|a / b| : ℚ) : ℝ) := by rw [hvec.1, hvec.2.1, hratio a b hb]
  have hn12 : ‖e 1 / e 2‖ = ((|b / c'| : ℚ) : ℝ) := by rw [hvec.2.1, hvec.2.2, hratio b c' hc]
  have hn02 : ‖e 0 / e 2‖ = ((|a / c'| : ℚ) : ℝ) := by rw [hvec.1, hvec.2.2, hratio a c' hc]
  have hbox := box_conj_shear e he (algebraMap ℚ w₀.Completion s) C hC1
    (by rw [hn01]; exact_mod_cast r01) (by rw [hn12]; exact_mod_cast r12)
    (by rw [hn02, hρ]; exact r02)
    (A n : Matrix (Fin 3) (Fin 3) w₀.Completion) (fun i => (hn_box i i).1) (fun i j hij => (hn_box i j).2.1 hij)
    (fun i j => (hn_box i j).2.2)
  have hroots : archRoot₁ ℚ w₀ (D * t) = |a / b| * archRoot₁ ℚ w₀ t ∧
      archRoot₂ ℚ w₀ (D * t) = |b / c'| * archRoot₂ ℚ w₀ t := by
    have h₁ := rootSizes_of_coe_eq_diagonal (A (D * t)) _ hADt_coe (mul_ne_zero (he 1) (hdne 1))
      (mul_ne_zero (he 2) (hdne 2))
    have h₀ := rootSizes_of_coe_eq_diagonal (A t) d hT (hdne 1) (hdne 2)
    unfold archRoot₁ archRoot₂
    rw [hA, hA, h₁.1, h₁.2, h₀.1, h₀.2]
    simp only [norm_mul, he_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, hρ]
    constructor
    · rw [abs_div, mul_div_mul_comm, Rat.cast_div]
    · rw [abs_div, mul_div_mul_comm, Rat.cast_div]
  refine ⟨⟨?_, ?_, hk_fin, ?_⟩, hroots⟩
  · intro p
    rw [map_mul, map_mul, map_inv, hι_fin, hι_fin, hn_fin, one_mul, one_mul, inv_one]
  · intro p
    rw [map_mul, hι_fin, ht_fin, one_mul]
  · intro w
    obtain rfl := hw w
    rw [hA, hA, hAn', hADt_coe]
    refine ⟨fun i j => ⟨hu1 i, fun hij => hu0 i j hij, ?_⟩, fun i j hij => Matrix.diagonal_apply_ne _ hij, ?_, ?_, ?_⟩
    · have := hbox i j
      simpa only [Matrix.mul_assoc] using this
    · rw [hroots.1]
      exact hr₁
    · rw [hroots.2]
      exact hr₂
    · exact hk_orth

include hAι hA hρ in

private theorem witness_separate (a b c' : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c' ≠ 0) (s₁ s₂ : ℚ) {c C : ℝ}
    {n t k n' t' k' : AdelicGL 3 (𝓞 ℚ) ℚ} (hW : IsWitness c C n t k) (hW' : IsWitness c C n' t' k')
    (heq : ι (upperUnipotent3 0 0 (algebraMap ℚ w₀.Completion s₁) * devDiag w₀ a b c' ha hb hc) * (n * t * k) =
      ι (upperUnipotent3 0 0 (algebraMap ℚ w₀.Completion s₂) * devDiag w₀ a b c' ha hb hc) * (n' * t' * k')) :
    |s₁ - s₂| ≤ |a / c'| * (2 * C) := by
  set e : Fin 3 → w₀.Completion :=
    ![algebraMap ℚ w₀.Completion a, algebraMap ℚ w₀.Completion b, algebraMap ℚ w₀.Completion c'] with he_def
  have he : ∀ i, e i ≠ 0 := devDiag_entries_ne_zero w₀ a b c' ha hb hc
  have key : ∀ (s : ℚ) {m u l : AdelicGL 3 (𝓞 ℚ) ℚ}, IsWitness c C m u l →
      gramZeta ((A (ι (upperUnipotent3 0 0 (algebraMap ℚ w₀.Completion s) * devDiag w₀ a b c' ha hb hc) *
          (m * u * l)) : GL (Fin 3) w₀.Completion) : Matrix (Fin 3) (Fin 3) w₀.Completion) =
        e 0 / e 2 * (A m : Matrix (Fin 3) (Fin 3) w₀.Completion) 0 2 + algebraMap ℚ w₀.Completion s := by
    intro s m u l hV
    obtain ⟨-, -, -, harch⟩ := hV
    obtain ⟨hm_box, hu_off, -, -, hl_orth⟩ := harch w₀
    rw [hA] at hm_box hu_off hl_orth
    set d : Fin 3 → w₀.Completion := fun i => (A u : Matrix (Fin 3) (Fin 3) w₀.Completion) i i with hd_def
    have hU : (A u : Matrix (Fin 3) (Fin 3) w₀.Completion) = Matrix.diagonal d :=
      eq_diagonal_of_offDiag_eq_zero _ hu_off
    have hd2 : d 2 ≠ 0 := diag_entries_ne_zero w₀ (A u) d hU 2
    set N : Matrix (Fin 3) (Fin 3) w₀.Completion := (A m : Matrix (Fin 3) (Fin 3) w₀.Completion) with hN_def
    have h20 : N 2 0 = 0 := (hm_box 2 0).2.1 (by decide)
    have h21 : N 2 1 = 0 := (hm_box 2 1).2.1 (by decide)
    have h22 : N 2 2 = 1 := (hm_box 2 2).1
    have hNU_row : ∀ j, (N * Matrix.diagonal d) 2 j = Matrix.diagonal d 2 j :=
      mul_apply_two_of_last_row N _ h20 h21 h22
    have hdenNU : (N * Matrix.diagonal d) 2 0 * (N * Matrix.diagonal d) 2 0 +
        (N * Matrix.diagonal d) 2 1 * (N * Matrix.diagonal d) 2 1 +
        (N * Matrix.diagonal d) 2 2 * (N * Matrix.diagonal d) 2 2 ≠ 0 := by
      simp only [hNU_row, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (show (2 : Fin 3) ≠ 0 by decide),
        Matrix.diagonal_apply_ne _ (show (2 : Fin 3) ≠ 1 by decide), mul_zero, zero_add]
      exact mul_ne_zero hd2 hd2
    have hdenE : (Matrix.diagonal e * (N * Matrix.diagonal d)) 2 0 *
          (Matrix.diagonal e * (N * Matrix.diagonal d)) 2 0 +
        (Matrix.diagonal e * (N * Matrix.diagonal d)) 2 1 * (Matrix.diagonal e * (N * Matrix.diagonal d)) 2 1 +
        (Matrix.diagonal e * (N * Matrix.diagonal d)) 2 2 * (Matrix.diagonal e * (N * Matrix.diagonal d)) 2 2 ≠ 0 := by
      simp only [Matrix.diagonal_mul, hNU_row, Matrix.diagonal_apply_eq,
        Matrix.diagonal_apply_ne _ (show (2 : Fin 3) ≠ 0 by decide),
        Matrix.diagonal_apply_ne _ (show (2 : Fin 3) ≠ 1 by decide), mul_zero, zero_add]
      exact mul_ne_zero (mul_ne_zero (he 2) hd2) (mul_ne_zero (he 2) hd2)
    have hcoe : ((A (ι (upperUnipotent3 0 0 (algebraMap ℚ w₀.Completion s) * devDiag w₀ a b c' ha hb hc) *
        (m * u * l)) : GL (Fin 3) w₀.Completion) : Matrix (Fin 3) (Fin 3) w₀.Completion) =
        !![(1 : w₀.Completion), 0, algebraMap ℚ w₀.Completion s; 0, 1, 0; 0, 0, 1] *
          (Matrix.diagonal e * (N * Matrix.diagonal d)) * (A l : Matrix (Fin 3) (Fin 3) w₀.Completion) := by
      rw [map_mul, hAι, map_mul, map_mul, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
        upperUnipotent3_coe, devDiag_coe, hU]
      simp only [Matrix.mul_assoc, he_def, hN_def]
    rw [hcoe, gramZeta_mul_of_transpose_mul_eq_one _ _ hl_orth, gramZeta_shear_mul _ _ hdenE,
      gramZeta_diagonal_mul e (he 2) _ hdenNU, gramZeta_mul_diagonal_of_last_row N h20 h21 h22 d hd2]
  have h₁ := key s₁ hW
  have h₂ := key s₂ hW'
  rw [heq] at h₁
  rw [h₁] at h₂
  have hdiff : algebraMap ℚ w₀.Completion (s₁ - s₂) =
      e 0 / e 2 * ((A n' : Matrix (Fin 3) (Fin 3) w₀.Completion) 0 2 -
        (A n : Matrix (Fin 3) (Fin 3) w₀.Completion) 0 2) := by
    rw [map_sub]
    linear_combination h₂
  have hbound : ‖(A n : Matrix (Fin 3) (Fin 3) w₀.Completion) 0 2 -
      (A n' : Matrix (Fin 3) (Fin 3) w₀.Completion) 0 2‖ ≤
      2 * C := by
    have h := (hW.2.2.2 w₀).1 0 2
    have h' := (hW'.2.2.2 w₀).1 0 2
    rw [hA] at h h'
    calc _ ≤ ‖(A n : Matrix (Fin 3) (Fin 3) w₀.Completion) 0 2‖ +
          ‖(A n' : Matrix (Fin 3) (Fin 3) w₀.Completion) 0 2‖ :=
          norm_sub_le _ _
      _ ≤ C + C := add_le_add h.2.2 h'.2.2
      _ = 2 * C := by ring
  have hnorm : ‖e 0 / e 2‖ = |a / c'| := by
    simp only [he_def, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [← map_div₀, hρ]
  calc |s₁ - s₂| = ‖algebraMap ℚ w₀.Completion (s₁ - s₂)‖ := (hρ _).symm
    _ = ‖e 0 / e 2‖ * ‖(A n' : Matrix (Fin 3) (Fin 3) w₀.Completion) 0 2 -
          (A n : Matrix (Fin 3) (Fin 3) w₀.Completion) 0 2‖ := by rw [hdiff, norm_mul]
    _ = ‖e 0 / e 2‖ * ‖(A n : Matrix (Fin 3) (Fin 3) w₀.Completion) 0 2 -
          (A n' : Matrix (Fin 3) (Fin 3) w₀.Completion) 0 2‖ := by rw [norm_sub_rev]
    _ ≤ |a / c'| * (2 * C) := by
          rw [hnorm]
          exact mul_le_mul_of_nonneg_left hbound (by positivity)

end Device

end SiegelContraction

end

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField Matrix LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.LanglandsTunnell.CubicInduction"

noncomputable section

namespace SiegelContraction

section Transport

variable (w₀ : InfinitePlace ℚ) (e : w₀.Completion ≃+* ℝ) (he : ∀ r : ℝ, ‖e.symm r‖ = ‖r‖)

include he in
private theorem norm_eq_abs_apply (x : w₀.Completion) : ‖x‖ = |e x| := by
  have h := he (e x)
  rw [RingEquiv.symm_apply_apply, Real.norm_eq_abs] at h
  exact h

include he in

private theorem norm_algebraMap_rat (q : ℚ) : ‖algebraMap ℚ w₀.Completion q‖ = |q| := by
  rw [norm_eq_abs_apply w₀ e he]
  have h : e (algebraMap ℚ w₀.Completion q) = (q : ℝ) := by
    rw [show e (algebraMap ℚ w₀.Completion q) = (e.toRingHom.comp (algebraMap ℚ w₀.Completion)) q from rfl,
      eq_ratCast]
  rw [h, Rat.cast_abs]

private def toRealPlace (g : GL (Fin 3) w₀.Completion) : GL (Fin 3) ℝ :=
  Matrix.GeneralLinearGroup.map e.toRingHom g

private theorem toRealPlace_apply (g : GL (Fin 3) w₀.Completion) (i j : Fin 3) :
    ((toRealPlace w₀ e g : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) i j =
      e ((g : Matrix (Fin 3) (Fin 3) w₀.Completion) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

private theorem toRealPlace_mul (g h : GL (Fin 3) w₀.Completion) :
    toRealPlace w₀ e (g * h) = toRealPlace w₀ e g * toRealPlace w₀ e h :=
  map_mul _ _ _

include he in
private theorem lastRowEucl_toRealPlace (g : GL (Fin 3) w₀.Completion) :
    lastRowEucl (toRealPlace w₀ e g) = lastRowEucl g := by
  unfold lastRowEucl
  simp only [toRealPlace_apply, Real.norm_eq_abs, norm_eq_abs_apply w₀ e he]

private theorem bottomMinor_toRealPlace (g : GL (Fin 3) w₀.Completion) (j j' : Fin 3) :
    bottomMinor (toRealPlace w₀ e g) j j' = e (bottomMinor g j j') := by
  unfold bottomMinor
  simp only [toRealPlace_apply, map_sub, map_mul]

include he in
private theorem minorEucl_toRealPlace (g : GL (Fin 3) w₀.Completion) :
    minorEucl (toRealPlace w₀ e g) = minorEucl g := by
  unfold minorEucl
  simp only [bottomMinor_toRealPlace, Real.norm_eq_abs, norm_eq_abs_apply w₀ e he]

include he in
private theorem detSize_toRealPlace (g : GL (Fin 3) w₀.Completion) : detSize (toRealPlace w₀ e g) = detSize g := by
  unfold detSize
  rw [norm_eq_abs_apply w₀ e he, Real.norm_eq_abs]
  congr 1
  show (e.toRingHom.mapMatrix (g : Matrix (Fin 3) (Fin 3) w₀.Completion)).det = e.toRingHom _
  rw [RingHom.map_det]

private theorem toRealPlace_orthogonal (k : GL (Fin 3) w₀.Completion)
    (hk : (k : Matrix (Fin 3) (Fin 3) w₀.Completion)ᵀ * (k : Matrix (Fin 3) (Fin 3) w₀.Completion) = 1) :
    ((toRealPlace w₀ e k : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *
        ((toRealPlace w₀ e k : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  have hcoe : ((toRealPlace w₀ e k : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) =
      (k : Matrix (Fin 3) (Fin 3) w₀.Completion).map e.toRingHom := by
    ext i j
    exact toRealPlace_apply w₀ e k i j
  rw [hcoe, ← Matrix.transpose_map, ← Matrix.map_mul, hk]
  exact Matrix.map_one _ (map_zero e.toRingHom) (map_one e.toRingHom)

include he in

private theorem sizes_mul_orthogonal (g k : GL (Fin 3) w₀.Completion)
    (hk : (k : Matrix (Fin 3) (Fin 3) w₀.Completion)ᵀ * (k : Matrix (Fin 3) (Fin 3) w₀.Completion) = 1) :
    lastRowEucl (g * k) = lastRowEucl g ∧ minorEucl (g * k) = minorEucl g ∧ detSize (g * k) = detSize g := by
  have hkR := toRealPlace_orthogonal w₀ e k hk
  refine ⟨?_, ?_, ?_⟩
  · rw [← lastRowEucl_toRealPlace w₀ e he, toRealPlace_mul, lastRowEucl_mul_of_transpose_mul_eq_one _ _ hkR,
      lastRowEucl_toRealPlace w₀ e he]
  · rw [← minorEucl_toRealPlace w₀ e he, toRealPlace_mul, minorEucl_mul_of_transpose_mul_eq_one _ _ hkR,
      minorEucl_toRealPlace w₀ e he]
  · rw [← detSize_toRealPlace w₀ e he, toRealPlace_mul, detSize_mul_of_transpose_mul_eq_one _ _ hkR,
      detSize_toRealPlace w₀ e he]

end Transport

section Bridge

variable {L : Type*} [NormedField L]

private theorem eq_upperUnipotent3_of_unitriangular (N : GL (Fin 3) L)
    (h1 : ∀ i, (N : Matrix (Fin 3) (Fin 3) L) i i = 1)
    (h0 : ∀ i j : Fin 3, j < i → (N : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    N = upperUnipotent3 ((N : Matrix (Fin 3) (Fin 3) L) 0 1) ((N : Matrix (Fin 3) (Fin 3) L) 1 2)
      ((N : Matrix (Fin 3) (Fin 3) L) 0 2) := by
  have h10 := h0 1 0 (by decide)
  have h20 := h0 2 0 (by decide)
  have h21 := h0 2 1 (by decide)
  have h00 := h1 0
  have h11 := h1 1
  have h22 := h1 2
  ext i j
  rw [upperUnipotent3_coe]
  fin_cases i <;> fin_cases j <;> simp [h10, h20, h21, h00, h11, h22]

private theorem sizes_unitriangular_mul (N g : GL (Fin 3) L) (h1 : ∀ i, (N : Matrix (Fin 3) (Fin 3) L) i i = 1)
    (h0 : ∀ i j : Fin 3, j < i → (N : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    lastRowEucl (N * g) = lastRowEucl g ∧ minorEucl (N * g) = minorEucl g ∧ detSize (N * g) = detSize g := by
  rw [eq_upperUnipotent3_of_unitriangular N h1 h0]
  exact ⟨lastRowEucl_upperUnipotent3_mul _ _ _ _, minorEucl_upperUnipotent3_mul _ _ _ _,
    detSize_upperUnipotent3_mul _ _ _ _⟩

end Bridge

section Roots

variable (w₀ : InfinitePlace ℚ) (e : w₀.Completion ≃+* ℝ) (he : ∀ r : ℝ, ‖e.symm r‖ = ‖r‖)

include he in

private theorem archRoot_mul_eq_of_witness {c C : ℝ} {n t k : AdelicGL 3 (𝓞 ℚ) ℚ} (hW : IsWitness c C n t k) :
    archRoot₁ ℚ w₀ (n * t * k) = archRoot₁ ℚ w₀ t ∧ archRoot₂ ℚ w₀ (n * t * k) = archRoot₂ ℚ w₀ t := by
  obtain ⟨-, -, -, harch⟩ := hW
  obtain ⟨hn_box, -, -, -, hk_orth⟩ := harch w₀
  have hprod : archPlaceComponent3 ℚ w₀ (n * t * k) =
      archPlaceComponent3 ℚ w₀ n * (archPlaceComponent3 ℚ w₀ t * archPlaceComponent3 ℚ w₀ k) := by
    rw [map_mul, map_mul, mul_assoc]
  obtain ⟨hl₁, hm₁, hd₁⟩ := sizes_unitriangular_mul (archPlaceComponent3 ℚ w₀ n)
    (archPlaceComponent3 ℚ w₀ t * archPlaceComponent3 ℚ w₀ k) (fun i => (hn_box i i).1)
    (fun i j hij => (hn_box i j).2.1 hij)
  obtain ⟨hl₂, hm₂, hd₂⟩ := sizes_mul_orthogonal w₀ e he (archPlaceComponent3 ℚ w₀ t) (archPlaceComponent3 ℚ w₀ k)
    hk_orth
  unfold archRoot₁ archRoot₂
  rw [hprod, hl₁, hm₁, hd₁, hl₂, hm₂, hd₂]
  exact ⟨rfl, rfl⟩

end Roots

end SiegelContraction

end

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField Matrix LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.LanglandsTunnell.CubicInduction"

noncomputable section

namespace SiegelContraction

section SetGrade

variable (w₀ : InfinitePlace ℚ) (e : w₀.Completion ≃+* ℝ) (he : ∀ r : ℝ, ‖e.symm r‖ = ‖r‖)
  (ι : GL (Fin 3) w₀.Completion →* AdelicGL 3 (𝓞 ℚ) ℚ)
  (hw : ∀ w : InfinitePlace ℚ, w = w₀)
  (hι_fin : ∀ (u : GL (Fin 3) w₀.Completion) (p : HeightOneSpectrum (𝓞 ℚ)), componentAt3 (𝓞 ℚ) ℚ p (ι u) = 1)
  (hAι : ∀ u : GL (Fin 3) w₀.Completion, archPlaceComponent3 ℚ w₀ (ι u) = u)

private def deviceElt (a b c' : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c' ≠ 0) (s : ℚ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  ι (upperUnipotent3 0 0 (algebraMap ℚ w₀.Completion s) * devDiag w₀ a b c' ha hb hc)

private theorem mem_siegelSet_iff (c C : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    g ∈ siegelSet c C ↔ ∃ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, g = n * t * k ∧ IsWitness c C n t k :=
  Iff.rfl

include he hw hι_fin hAι in

private theorem deviceElt_mul_mem (a b c' : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c' ≠ 0) (s : ℚ) {c C : ℝ}
    (r01 : |a / b| ≤ 1) (r12 : |b / c'| ≤ 1) (r02 : |a / c'| * C + |s| ≤ C)
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : g ∈ siegelSet c C)
    (hr₁ : c ≤ |a / b| * archRoot₁ ℚ w₀ g) (hr₂ : c ≤ |b / c'| * archRoot₂ ℚ w₀ g) :
    deviceElt w₀ ι a b c' ha hb hc s * g ∈ siegelSet c C ∧
      archRoot₁ ℚ w₀ (deviceElt w₀ ι a b c' ha hb hc s * g) = |a / b| * archRoot₁ ℚ w₀ g ∧
      archRoot₂ ℚ w₀ (deviceElt w₀ ι a b c' ha hb hc s * g) = |b / c'| * archRoot₂ ℚ w₀ g := by
  obtain ⟨n, t, k, rfl, hW⟩ := hg
  obtain ⟨hb₁, hb₂⟩ := archRoot_mul_eq_of_witness w₀ e he hW
  rw [hb₁] at hr₁
  rw [hb₂] at hr₂
  obtain ⟨hW', hρ₁, hρ₂⟩ := witness_contract w₀ ι (archPlaceComponent3 ℚ w₀) hw hι_fin hAι (fun _ => rfl)
    (norm_algebraMap_rat w₀ e he) a b c' ha hb hc s r01 r12 r02 hW hr₁ hr₂
  have hfactor : deviceElt w₀ ι a b c' ha hb hc s * (n * t * k) =
      (ι (upperUnipotent3 0 0 (algebraMap ℚ w₀.Completion s) * devDiag w₀ a b c' ha hb hc) * n *
          (ι (devDiag w₀ a b c' ha hb hc))⁻¹) *
        (ι (devDiag w₀ a b c' ha hb hc) * t) * k :=
    device_mul_eq _ _ _ _ _
  obtain ⟨hb₁', hb₂'⟩ := archRoot_mul_eq_of_witness w₀ e he hW'
  refine ⟨⟨_, _, _, hfactor, hW'⟩, ?_, ?_⟩
  · rw [hfactor, hb₁', hρ₁, hb₁]
  · rw [hfactor, hb₂', hρ₂, hb₂]

include he hAι in

private theorem deviceElt_mul_ne (a b c' : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c' ≠ 0) (s₁ s₂ : ℚ) {c C : ℝ}
    (hsep : |a / c'| * (2 * C) < |s₁ - s₂|)
    {g g' : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : g ∈ siegelSet c C) (hg' : g' ∈ siegelSet c C) :
    deviceElt w₀ ι a b c' ha hb hc s₁ * g ≠ deviceElt w₀ ι a b c' ha hb hc s₂ * g' := by
  obtain ⟨n, t, k, rfl, hW⟩ := hg
  obtain ⟨n', t', k', rfl, hW'⟩ := hg'
  intro heq
  have h := witness_separate w₀ ι (archPlaceComponent3 ℚ w₀) hAι (fun _ => rfl) (norm_algebraMap_rat w₀ e he)
    a b c' ha hb hc s₁ s₂ hW hW' heq
  exact absurd h (not_le.2 hsep)

include he in

private theorem le_archRoot_of_mem {c C : ℝ} {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : g ∈ siegelSet c C) :
    c ≤ archRoot₁ ℚ w₀ g ∧ c ≤ archRoot₂ ℚ w₀ g := by
  obtain ⟨n, t, k, rfl, hW⟩ := hg
  obtain ⟨hb₁, hb₂⟩ := archRoot_mul_eq_of_witness w₀ e he hW
  rw [hb₁, hb₂]
  exact ⟨(hW.2.2.2 w₀).2.2.1, (hW.2.2.2 w₀).2.2.2.1⟩

private theorem ideleNorm_det_deviceElt_mul
    (hmul : ∀ x y : AdelicGL 3 (𝓞 ℚ) ℚ, NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x * y)) =
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det x) *
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det y))
    (hone : ∀ u : GL (Fin 3) w₀.Completion, ‖(u : Matrix (Fin 3) (Fin 3) w₀.Completion).det‖ = 1 →
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (ι u)) = 1)
    (hρ : ∀ q : ℚ, ‖algebraMap ℚ w₀.Completion q‖ = |q|)
    (a b c' : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c' ≠ 0) (hdet : |a * b * c'| = 1) (s : ℚ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (deviceElt w₀ ι a b c' ha hb hc s * g)) =
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by
  rw [hmul, deviceElt, hone, one_mul]
  rw [Units.val_mul, Matrix.det_mul, upperUnipotent3_coe, devDiag_coe, Matrix.det_fin_three, Matrix.det_diagonal,
    Fin.prod_univ_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, mul_one, mul_zero, zero_mul,
    sub_zero, add_zero, one_mul, ← map_mul]
  simp only [Matrix.vecHead, mul_zero, sub_zero, one_mul, hρ]
  exact_mod_cast hdet

end SetGrade

private theorem stage_one_ratios :
    |(1 / 4 : ℚ) / 2| ≤ 1 ∧ |(2 : ℚ) / 2| ≤ 1 ∧ |(1 / 4 : ℚ) / 2| = 1 / 8 ∧ |(2 : ℚ) / 2| = 1 ∧
    |(1 / 4 : ℚ) * 2 * 2| = 1 := by
  norm_num [abs_of_pos]

private theorem stage_two_ratios : |(1 / 2 : ℚ) / (1 / 2)| ≤ 1 ∧ |(1 / 2 : ℚ) / 4| ≤ 1 ∧ |(1 / 2 : ℚ) / (1 / 2)| = 1 ∧
    |(1 / 2 : ℚ) / 4| = 1 / 8 ∧ |(1 / 2 : ℚ) * (1 / 2) * 4| = 1 := by
  norm_num [abs_of_pos]

private theorem exists_shear (ρ : ℚ) (hρ : |ρ| = 1 / 8) {C : ℝ} (hC : 1 ≤ C) :
    ∃ s : ℚ, |ρ| * C + |s| ≤ C ∧ |ρ| * (2 * C) < |s - -s| := by
  have hρ' : ((|ρ| : ℚ) : ℝ) = 1 / 8 := by
    rw [hρ]
    norm_num
  obtain ⟨s, hs₁, hs₂⟩ := exists_rat_btwn (show C / 8 < C / 4 by linarith)
  have hs0 : (0 : ℝ) < s := by linarith
  have hs0' : (0 : ℚ) < s := by exact_mod_cast hs0
  refine ⟨s, ?_, ?_⟩
  · rw [hρ', abs_of_pos hs0']
    linarith
  · rw [hρ', sub_neg_eq_add, abs_of_pos (by linarith : (0 : ℚ) < s + s)]
    push_cast
    linarith

end SiegelContraction

end

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "bottomMinor lastRowEucl minorEucl detSize archRoot₁ archRoot₂ archPlaceComponent3 AdelicGL globalPointsGL upperUnipotent3 upperUnipotent3_coe localMaximalCompact3 mem_localMaximalCompact3_iff componentAtN componentAt3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private def unitAdeles : Set (AdeleRing (𝓞 ℚ) ℚ) :=
  {a | a.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ ∧ ∀ w : InfinitePlace ℚ, ‖a.1 w‖ ≤ 1}

private theorem isCompact_unitAdeles : IsCompact unitAdeles :=
  AutomorphicForm.isCompact_setOf_integral_and_norm_le_one ℚ

private def unitEntryMatrices : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {k | (∀ i j, (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j ∈ unitAdeles) ∧
    ∀ i j, ((k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j ∈ unitAdeles}

private theorem isCompact_unitEntryMatrices : IsCompact unitEntryMatrices := by
  set C : Set (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := {m | ∀ i j, m i j ∈ unitAdeles} with hC_def
  have hC : IsCompact C := by
    have hpi : C = Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => unitAdeles := by
      ext m
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_unitAdeles
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
  have heq : unitEntryMatrices = (Units.embedProduct (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) ⁻¹'
      (C ×ˢ (MulOpposite.op '' C)) := by
    ext k
    simp only [unitEntryMatrices, hC_def, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
      Set.mem_prod, Set.mem_image, MulOpposite.op_inj, exists_eq_right]
  rw [heq]
  exact hK

private theorem snd_entry_mem_integralFiniteAdeles {k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) (i j : Fin 3) :
    ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ :=
  fun p => (hk p).1 i j

private theorem snd_entry_inv_mem_integralFiniteAdeles {k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) (i j : Fin 3) :
    (((k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 ∈
      AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ :=
  snd_entry_mem_integralFiniteAdeles
    (fun p => by rw [map_inv]; exact (localMaximalCompact3 (𝓞 ℚ) ℚ p).inv_mem (hk p)) i j

private theorem archPlaceComponent3_coe_apply (w : InfinitePlace ℚ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) i j =
      ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 w :=
  rfl

private theorem mem_unitEntryMatrices {k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (harch : ∀ (w : InfinitePlace ℚ) (i j : Fin 3),
      ‖(archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ 1)
    (harch' : ∀ (w : InfinitePlace ℚ) (i j : Fin 3),
      ‖(archPlaceComponent3 ℚ w k⁻¹ : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ 1) :
    k ∈ unitEntryMatrices :=
  ⟨fun i j => ⟨snd_entry_mem_integralFiniteAdeles hfin i j, fun w => harch w i j⟩,
    fun i j => ⟨snd_entry_inv_mem_integralFiniteAdeles hfin i j, fun w => harch' w i j⟩⟩

private theorem setOf_maximalCompactClauses_subset :
    {k : AdelicGL 3 (𝓞 ℚ) ℚ |
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
      (∀ (w : InfinitePlace ℚ) (i j : Fin 3),
        ‖(archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ 1) ∧
      ∀ (w : InfinitePlace ℚ) (i j : Fin 3),
        ‖(archPlaceComponent3 ℚ w k⁻¹ : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ 1} ⊆ unitEntryMatrices :=
  fun _ hk => mem_unitEntryMatrices hk.1 hk.2.1 hk.2.2

end LanglandsTunnell.CubicInduction

set_option autoImplicit false

open Matrix

noncomputable section

namespace SiegelSetTopology

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.LanglandsTunnell.CubicInduction"

section Sizes

variable {L : Type*} [NormedField L]

private theorem continuous_entry (i j : Fin 3) :
    Continuous fun k : GL (Fin 3) L => (k : Matrix (Fin 3) (Fin 3) L) i j :=
  Units.continuous_val.matrix_elem i j

private theorem continuous_detSize : Continuous fun k : GL (Fin 3) L => detSize k := by
  unfold detSize
  exact (Units.continuous_val.matrix_det).norm

private theorem continuous_lastRowEucl : Continuous fun k : GL (Fin 3) L => lastRowEucl k := by
  unfold lastRowEucl
  exact ((((continuous_entry 2 0).norm.pow 2).add ((continuous_entry 2 1).norm.pow 2)).add
    ((continuous_entry 2 2).norm.pow 2)).sqrt

private theorem continuous_bottomMinor (j j' : Fin 3) : Continuous fun k : GL (Fin 3) L => bottomMinor k j j' := by
  unfold bottomMinor
  exact ((continuous_entry 1 j).mul (continuous_entry 2 j')).sub ((continuous_entry 1 j').mul (continuous_entry 2 j))

private theorem continuous_minorEucl : Continuous fun k : GL (Fin 3) L => minorEucl k := by
  unfold minorEucl
  exact ((((continuous_bottomMinor 0 1).norm.pow 2).add ((continuous_bottomMinor 0 2).norm.pow 2)).add
    ((continuous_bottomMinor 1 2).norm.pow 2)).sqrt

private def rootCone (c : ℝ) : Set (GL (Fin 3) L) :=
  {t | (∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) L) i j = 0) ∧
    c * ‖(t : Matrix (Fin 3) (Fin 3) L) 1 1‖ ≤ ‖(t : Matrix (Fin 3) (Fin 3) L) 0 0‖ ∧
    c * ‖(t : Matrix (Fin 3) (Fin 3) L) 2 2‖ ≤ ‖(t : Matrix (Fin 3) (Fin 3) L) 1 1‖}

private theorem isClosed_rootCone (c : ℝ) : IsClosed (rootCone (L := L) c) := by
  unfold rootCone
  have hdiag : IsClosed {t : GL (Fin 3) L | ∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) L) i j = 0} := by
    have : {t : GL (Fin 3) L | ∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) L) i j = 0} =
        ⋂ i : Fin 3, ⋂ j : Fin 3, {t : GL (Fin 3) L | i ≠ j → (t : Matrix (Fin 3) (Fin 3) L) i j = 0} := by
      ext t; simp
    rw [this]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ne_eq, not_false_eq_true, true_implies]
      exact isClosed_eq (continuous_entry i j) continuous_const
  refine hdiag.inter (IsClosed.inter ?_ ?_)
  · exact isClosed_le (continuous_const.mul (continuous_entry 1 1).norm) (continuous_entry 0 0).norm
  · exact isClosed_le (continuous_const.mul (continuous_entry 2 2).norm) (continuous_entry 1 1).norm

private def unipotentBox (C : ℝ) : Set (GL (Fin 3) L) :=
  (fun p : L × L × L => upperUnipotent3 p.1 p.2.1 p.2.2) ''
    (Metric.closedBall (0 : L) C ×ˢ Metric.closedBall (0 : L) C ×ˢ Metric.closedBall (0 : L) C)

private theorem continuous_upperUnipotent3 :
    Continuous fun p : L × L × L => (upperUnipotent3 p.1 p.2.1 p.2.2 : GL (Fin 3) L) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

private theorem isCompact_unipotentBox [ProperSpace L] (C : ℝ) : IsCompact (unipotentBox (L := L) C) :=
  ((ProperSpace.isCompact_closedBall (0 : L) C).prod
    ((ProperSpace.isCompact_closedBall (0 : L) C).prod (ProperSpace.isCompact_closedBall (0 : L) C))).image
    continuous_upperUnipotent3

end Sizes

section Adelic

open NumberField IsDedekindDomain
open scoped Pointwise

private theorem continuous_glMap3 {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 3) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) : Continuous fun m : Matrix (Fin 3) (Fin 3) A => m.map f)

private theorem continuous_archPlaceComponent3 (w : InfinitePlace ℚ) : Continuous (archPlaceComponent3 ℚ w) := by
  unfold archPlaceComponent3
  rw [MonoidHom.coe_comp]
  exact (continuous_glMap3 _ (AdelicLevel.continuous_archEval ℚ w)).comp
    (continuous_glMap3 _ (AdelicLevel.continuous_adeleArch (R := 𝓞 ℚ) (K := ℚ)))

private theorem measurable_archRoot₁ (w : InfinitePlace ℚ) :
    @Measurable _ _ (AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ) _ (archRoot₁ ℚ w) := by
  letI := AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  have hA := continuous_archPlaceComponent3 w
  unfold archRoot₁
  exact ((continuous_detSize.comp hA).measurable.mul (continuous_lastRowEucl.comp hA).measurable).div
    ((continuous_minorEucl.comp hA).measurable.pow_const 2)

private theorem measurable_archRoot₂ (w : InfinitePlace ℚ) :
    @Measurable _ _ (AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ) _ (archRoot₂ ℚ w) := by
  letI := AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  have hA := continuous_archPlaceComponent3 w
  unfold archRoot₂
  exact (continuous_minorEucl.comp hA).measurable.div ((continuous_lastRowEucl.comp hA).measurable.pow_const 2)

variable (w : InfinitePlace ℚ) (ι : GL (Fin 3) w.Completion →* AdelicGL 3 (𝓞 ℚ) ℚ)

private theorem isClosed_finiteTrivial :
    IsClosed {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p g = 1} := by
  have : {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p g = 1} =
      ⋂ p : HeightOneSpectrum (𝓞 ℚ), {g | componentAt3 (𝓞 ℚ) ℚ p g = 1} := by
    ext g; simp
  rw [this]
  refine isClosed_iInter fun p => isClosed_eq ?_ continuous_const
  unfold componentAt3 componentAtN
  exact continuous_glMap3 _ ((AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ p).comp
    (AdelicLevel.continuous_adeleFin (R := 𝓞 ℚ) (K := ℚ)))

private theorem range_eq_finiteTrivial (hfin : ∀ u p, componentAt3 (𝓞 ℚ) ℚ p (ι u) = 1)
    (hrec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1) → ι (archPlaceComponent3 ℚ w g) = g) :
    Set.range ι = {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1} := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩ p
    exact hfin u p
  · intro hg
    exact ⟨_, hrec g hg⟩

private theorem image_eq_range_inter_preimage (hret : ∀ u, archPlaceComponent3 ℚ w (ι u) = u)
    (A : Set (GL (Fin 3) w.Completion)) : ι '' A = Set.range ι ∩ (archPlaceComponent3 ℚ w) ⁻¹' A := by
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, by simpa [hret u] using hu⟩
  · rintro ⟨⟨u, rfl⟩, hg⟩
    exact ⟨u, by simpa [hret u] using hg, rfl⟩

private theorem isClosed_image_of_isClosed (hfin : ∀ u p, componentAt3 (𝓞 ℚ) ℚ p (ι u) = 1)
    (hret : ∀ u, archPlaceComponent3 ℚ w (ι u) = u)
    (hrec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1) → ι (archPlaceComponent3 ℚ w g) = g)
    {A : Set (GL (Fin 3) w.Completion)} (hA : IsClosed A) : IsClosed (ι '' A) := by
  rw [image_eq_range_inter_preimage w ι hret, range_eq_finiteTrivial w ι hfin hrec]
  exact (isClosed_finiteTrivial).inter (hA.preimage (continuous_archPlaceComponent3 w))

private def structuredSet (c C : ℝ) (K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  ι '' unipotentBox C * (ι '' rootCone c * K)

private theorem isClosed_structuredSet (hι : Continuous ι) (hfin : ∀ u p, componentAt3 (𝓞 ℚ) ℚ p (ι u) = 1)
    (hret : ∀ u, archPlaceComponent3 ℚ w (ι u) = u)
    (hrec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1) → ι (archPlaceComponent3 ℚ w g) = g)
    (c C : ℝ) {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hK : IsCompact K) : IsClosed (structuredSet w ι c C K) := by
  haveI : ProperSpace w.Completion := AutomorphicForm.WindowedSiegel.properSpace_completion w
  have hbox : IsCompact (ι '' unipotentBox C) := (isCompact_unipotentBox C).image hι
  have hcone : IsClosed (ι '' rootCone c) := isClosed_image_of_isClosed w ι hfin hret hrec (isClosed_rootCone c)
  exact (hcone.mul_right_of_isCompact hK).mul_left_of_isCompact hbox

private theorem measurableSet_structuredSet (hι : Continuous ι) (hfin : ∀ u p, componentAt3 (𝓞 ℚ) ℚ p (ι u) = 1)
    (hret : ∀ u, archPlaceComponent3 ℚ w (ι u) = u)
    (hrec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1) → ι (archPlaceComponent3 ℚ w g) = g)
    (c C : ℝ) {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hK : IsCompact K) :
    @MeasurableSet _ (AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ) (structuredSet w ι c C K) := by
  letI := AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  exact (isClosed_structuredSet w ι hι hfin hret hrec c C hK).measurableSet

end Adelic

end SiegelSetTopology

end

set_option autoImplicit false

p2m_open "Matrix NumberField NumberField.AdelicLevel IsDedekindDomain LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.LanglandsTunnell.CubicInduction"

noncomputable section

namespace SiegelSlabCut

private theorem ideleNorm_eq_pow_mult_of_forall_norm_eq_one (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (w : InfinitePlace ℚ)
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), ‖(a : AdeleRing (𝓞 ℚ) ℚ).2 v‖ = 1) :
    TateGlobal.ideleNorm ℚ a = ‖(a : AdeleRing (𝓞 ℚ) ℚ).1 w‖ ^ w.mult := by
  unfold TateGlobal.ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm ℚ a,
    finprod_eq_one_of_forall_eq_one h, mul_one, Fintype.prod_unique, Subsingleton.elim (default : InfinitePlace ℚ) w]

private theorem mult_eq_one (w : InfinitePlace ℚ) : w.mult = 1 := by
  have hw : w.IsReal := by
    rw [Subsingleton.elim w Rat.infinitePlace]
    exact Rat.isReal_infinitePlace
  simp [InfinitePlace.mult, hw]

private theorem ideleNorm_eq_of_forall_norm_eq_one (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (w : InfinitePlace ℚ)
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), ‖(a : AdeleRing (𝓞 ℚ) ℚ).2 v‖ = 1) :
    TateGlobal.ideleNorm ℚ a = ‖(a : AdeleRing (𝓞 ℚ) ℚ).1 w‖ := by
  rw [ideleNorm_eq_pow_mult_of_forall_norm_eq_one a w h, mult_eq_one, pow_one]

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

private theorem valued_det_le_one {M : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)}
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) :
    Valued.v M.det ≤ 1 := by
  let M' : Matrix (Fin 3) (Fin 3) (p.adicCompletionIntegers ℚ) :=
    fun i j => ⟨M i j, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).2 (hM i j)⟩
  have hM' : (p.adicCompletionIntegers ℚ).subtype.mapMatrix M' = M := by
    ext i j
    rfl
  rw [← hM', ← RingHom.map_det]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).1 (Subtype.mem _)

private theorem norm_le_one_of_valued_le_one {x : p.adicCompletion ℚ} (hx : Valued.v x ≤ 1) : ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.2 hx

private theorem norm_det_eq_one_of_mem {k : GL (Fin 3) (p.adicCompletion ℚ)}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ‖(k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det‖ = 1 := by
  obtain ⟨h₁, h₂⟩ := (mem_localMaximalCompact3_iff (R := 𝓞 ℚ) (K := ℚ) (v := p)).1 hk
  have hd₁ : ‖(k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det‖ ≤ 1 :=
    norm_le_one_of_valued_le_one p (valued_det_le_one p h₁)
  have hd₂ : ‖((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det‖ ≤ 1 :=
    norm_le_one_of_valued_le_one p (valued_det_le_one p h₂)
  have hmul : (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det *
      ((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hnorm : ‖(k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det‖ *
      ‖((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hpos : 0 ≤ ‖(k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det‖ := norm_nonneg _
  nlinarith [hd₁, hd₂, hnorm, hpos, norm_nonneg
    ((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det]

end Local

private theorem det_snd_apply (g : AdelicGL 3 (𝓞 ℚ) ℚ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 p =
      (componentAt3 (𝓞 ℚ) ℚ p g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det := by
  show finAdeleEval (𝓞 ℚ) ℚ p (adeleFin (𝓞 ℚ) ℚ (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).det) = _
  rw [RingHom.map_det, RingHom.map_det]
  rfl

private theorem det_fst_apply (g : AdelicGL 3 (𝓞 ℚ) ℚ) (w : InfinitePlace ℚ) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 w =
      (archPlaceComponent3 ℚ w g : Matrix (Fin 3) (Fin 3) w.Completion).det := by
  show archEval ℚ w (adeleArch (𝓞 ℚ) ℚ (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).det) = _
  rw [RingHom.map_det, RingHom.map_det]
  rfl

private theorem ideleNorm_det_eq (w : InfinitePlace ℚ) {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) =
      ‖(archPlaceComponent3 ℚ w g : Matrix (Fin 3) (Fin 3) w.Completion).det‖ := by
  rw [ideleNorm_eq_of_forall_norm_eq_one _ w, det_fst_apply]
  intro p
  rw [det_snd_apply]
  exact norm_det_eq_one_of_mem p (hg p)

private theorem isClosed_setOf_norm_det_mem_Icc (w : InfinitePlace ℚ) (hcont : Continuous (archPlaceComponent3 ℚ w))
    (a b : ℝ) :
    IsClosed {g : AdelicGL 3 (𝓞 ℚ) ℚ |
      ‖(archPlaceComponent3 ℚ w g : Matrix (Fin 3) (Fin 3) w.Completion).det‖ ∈ Set.Icc a b} :=
  isClosed_Icc.preimage (Continuous.matrix_det (Units.continuous_val.comp hcont)).norm

private theorem inter_slab_eq (w : InfinitePlace ℚ) (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hS : ∀ g ∈ S, ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (a b : ℝ) :
    S ∩ {g | TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} =
      S ∩ {g | ‖(archPlaceComponent3 ℚ w g : Matrix (Fin 3) (Fin 3) w.Completion).det‖ ∈ Set.Icc a b} := by
  ext g
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hgS, hg⟩
    exact ⟨hgS, by rwa [ideleNorm_det_eq w (hS g hgS)] at hg⟩
  · rintro ⟨hgS, hg⟩
    exact ⟨hgS, by rwa [ideleNorm_det_eq w (hS g hgS)]⟩

end SiegelSlabCut

end

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.LanglandsTunnell.CubicInduction"
open SiegelGram SiegelContraction SiegelSetTopology SiegelSlabCut
open scoped Pointwise

noncomputable section

namespace SiegelSetBlock

section Determinants

variable {L : Type*} [NormedField L]

private theorem det_eq_one_of_unitriangular (M : Matrix (Fin 3) (Fin 3) L) (h1 : ∀ i, M i i = 1)
    (h0 : ∀ i j : Fin 3, j < i → M i j = 0) : M.det = 1 := by
  have h10 := h0 1 0 (by decide)
  have h20 := h0 2 0 (by decide)
  have h21 := h0 2 1 (by decide)
  simp [Matrix.det_fin_three, h1 0, h1 1, h1 2, h10, h20, h21]

private theorem norm_det_eq_one_of_transpose_mul_eq_one (M : Matrix (Fin 3) (Fin 3) L) (hM : Mᵀ * M = 1) :
    ‖M.det‖ = 1 := by
  have h := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have h' : ‖M.det‖ * ‖M.det‖ = 1 := by rw [← norm_mul, h, norm_one]
  rcases mul_self_eq_one_iff.1 h' with h'' | h''
  · exact h''
  · exfalso
    linarith [norm_nonneg M.det]

end Determinants

section Slice

variable {L : Type*} [NormedField L]

private def windowSlice (c K' a b : ℝ) : Set (GL (Fin 3) L) :=
  rootCone c ∩
    {t | ‖(t : Matrix (Fin 3) (Fin 3) L) 0 0‖ ≤ K' * ‖(t : Matrix (Fin 3) (Fin 3) L) 1 1‖ ∧
      ‖(t : Matrix (Fin 3) (Fin 3) L) 1 1‖ ≤ K' * ‖(t : Matrix (Fin 3) (Fin 3) L) 2 2‖} ∩
    {t | ‖(t : Matrix (Fin 3) (Fin 3) L).det‖ ∈ Set.Icc a b}

private theorem isClosed_windowSlice (c K' a b : ℝ) : IsClosed (windowSlice (L := L) c K' a b) := by
  unfold windowSlice
  refine ((isClosed_rootCone (L := L) c).inter (IsClosed.inter ?_ ?_)).inter ?_
  · exact isClosed_le (continuous_entry 0 0).norm (continuous_const.mul (continuous_entry 1 1).norm)
  · exact isClosed_le (continuous_entry 1 1).norm (continuous_const.mul (continuous_entry 2 2).norm)
  · exact isClosed_Icc.preimage Units.continuous_val.matrix_det.norm

private theorem isCompact_windowSlice [ProperSpace L] {c K' a : ℝ} (hc : 0 < c) (hK' : 0 < K') (ha : 0 < a) (b : ℝ) :
    IsCompact (windowSlice (L := L) c K' a b) := by
  obtain ⟨U, hU_def⟩ : ∃ U : ℝ, U = max 1 (b / c ^ 3) := ⟨_, rfl⟩
  have hU : 0 < U := by
    rw [hU_def]
    exact lt_of_lt_of_le one_pos (le_max_left _ _)
  have hKU : 0 ≤ K' * U := by positivity
  have hK2U : 0 ≤ K' ^ 2 * U := by positivity
  obtain ⟨hi, hhi_def⟩ : ∃ hi : ℝ, hi = K' ^ 2 * U + K' * U + U := ⟨_, rfl⟩
  have hhi : 0 < hi := by
    rw [hhi_def]
    positivity
  obtain ⟨lo, hlo_def⟩ : ∃ lo : ℝ,
      lo = min (a / (K' * U * U)) (min (a / (K' ^ 2 * U * U)) (a / (K' ^ 2 * U * (K' * U)))) := ⟨_, rfl⟩
  have hlo : 0 < lo := by
    rw [hlo_def]
    positivity
  have hlo₀ : lo ≤ a / (K' * U * U) := by
    rw [hlo_def]
    exact min_le_left _ _
  have hlo₁ : lo ≤ a / (K' ^ 2 * U * U) := by
    rw [hlo_def]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hlo₂ : lo ≤ a / (K' ^ 2 * U * (K' * U)) := by
    rw [hlo_def]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hB : IsCompact (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 =>
      Metric.closedBall (0 : L) hi) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ProperSpace.isCompact_closedBall _ _
  have hB' : IsCompact (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 =>
      Metric.closedBall (0 : L) lo⁻¹) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ProperSpace.isCompact_closedBall _ _
  have hKc : IsCompact ((Units.embedProduct (Matrix (Fin 3) (Fin 3) L)) ⁻¹'
      ((Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => Metric.closedBall (0 : L) hi) ×ˢ
        (MulOpposite.op '' (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 =>
          Metric.closedBall (0 : L) lo⁻¹)))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hB.prod (hB'.image MulOpposite.continuous_op))
  refine hKc.of_isClosed_subset (isClosed_windowSlice c K' a b) ?_
  rintro t ⟨⟨⟨hoff, hr₁, hr₂⟩, hu₁, hu₂⟩, hdet⟩
  have hdiag : (t : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (t : Matrix (Fin 3) (Fin 3) L) i i :=
    eq_diagonal_of_offDiag_eq_zero (t : Matrix (Fin 3) (Fin 3) L) hoff
  have hdet' : ‖(t : Matrix (Fin 3) (Fin 3) L) 0 0‖ * ‖(t : Matrix (Fin 3) (Fin 3) L) 1 1‖ *
      ‖(t : Matrix (Fin 3) (Fin 3) L) 2 2‖ ∈ Set.Icc a b := by
    rw [Set.mem_setOf_eq] at hdet
    rwa [hdiag, Matrix.det_diagonal, Fin.prod_univ_three, norm_mul, norm_mul] at hdet
  have hle := slice_sizes_le hc hK'.le (norm_nonneg _) hr₁ hr₂ hu₁ hu₂ hdet'.2
  have hge := slice_sizes_ge hc hK' ha (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hr₁ hr₂ hu₁ hu₂
    hdet'.1 hdet'.2
  rw [← hU_def] at hle hge
  have h0 : ‖(t : Matrix (Fin 3) (Fin 3) L) 0 0‖ ≤ hi := by
    rw [hhi_def]
    linarith [hle.2.2]
  have h1 : ‖(t : Matrix (Fin 3) (Fin 3) L) 1 1‖ ≤ hi := by
    rw [hhi_def]
    linarith [hle.2.1]
  have h2 : ‖(t : Matrix (Fin 3) (Fin 3) L) 2 2‖ ≤ hi := by
    rw [hhi_def]
    linarith [hle.1]
  have hdiag_le : ∀ i, ‖(t : Matrix (Fin 3) (Fin 3) L) i i‖ ≤ hi := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have g0 : lo ≤ ‖(t : Matrix (Fin 3) (Fin 3) L) 0 0‖ := hlo₀.trans hge.2.2
  have g1 : lo ≤ ‖(t : Matrix (Fin 3) (Fin 3) L) 1 1‖ := hlo₁.trans hge.2.1
  have g2 : lo ≤ ‖(t : Matrix (Fin 3) (Fin 3) L) 2 2‖ := hlo₂.trans hge.1
  have hdiag_ge : ∀ i, lo ≤ ‖(t : Matrix (Fin 3) (Fin 3) L) i i‖ := by
    intro i
    fin_cases i
    · exact g0
    · exact g1
    · exact g2
  have hne : ∀ i, (t : Matrix (Fin 3) (Fin 3) L) i i ≠ 0 := fun i =>
    norm_pos_iff.1 (hlo.trans_le (hdiag_ge i))
  have hinv : ((t⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => ((t : Matrix (Fin 3) (Fin 3) L) i i)⁻¹ :=
    coe_inv_of_coe_eq_diagonal t _ hne hdiag
  have hent : ∀ i j, ‖(t : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ hi := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact hdiag_le _
    · rw [hdiag, Matrix.diagonal_apply_ne _ hij, norm_zero]
      exact hhi.le
  have hinv_ent : ∀ i j, ‖((t⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖ ≤ lo⁻¹ := by
    intro i j
    rw [hinv]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, norm_inv]
      exact inv_anti₀ hlo (hdiag_ge _)
    · rw [Matrix.diagonal_apply_ne _ hij, norm_zero]
      exact inv_nonneg.2 hlo.le
  refine ⟨fun i _ => fun j _ => ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    exact hent i j
  · refine ⟨((t⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L), fun i _ => fun j _ => ?_, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact hinv_ent i j

end Slice

section Adelic

private def kSet : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {k | (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
    ∀ w : InfinitePlace ℚ,
      (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
        (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1}

private theorem mem_kSet_of_witness {c C : ℝ} {n t k : AdelicGL 3 (𝓞 ℚ) ℚ} (hW : IsWitness c C n t k) : k ∈ kSet :=
  ⟨hW.2.2.1, fun w => (hW.2.2.2 w).2.2.2.2⟩

private theorem one_le_of_witness (w : InfinitePlace ℚ) {c C : ℝ} {n t k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hW : IsWitness c C n t k) : 1 ≤ C := by
  have h := ((hW.2.2.2 w).1 0 0).2.2
  rwa [((hW.2.2.2 w).1 0 0).1, norm_one] at h

private theorem mem_localMaximalCompact3_of_mem_siegelSet {c C : ℝ} {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : g ∈ siegelSet c C)
    (p : HeightOneSpectrum (𝓞 ℚ)) : componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  obtain ⟨n, t, k, rfl, hW⟩ := hg
  obtain ⟨hn, ht, hk, -⟩ := hW
  simp only [map_mul, hn p, ht p, one_mul]
  exact hk p

private theorem siegelSet_inter_slab_eq (w : InfinitePlace ℚ) (c C a b : ℝ) :
    siegelSet c C ∩ {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} =
      siegelSet c C ∩
        {g | ‖(archPlaceComponent3 ℚ w g : Matrix (Fin 3) (Fin 3) w.Completion).det‖ ∈ Set.Icc a b} :=
  inter_slab_eq w (siegelSet c C) (fun _ hg p => mem_localMaximalCompact3_of_mem_siegelSet hg p) a b

private theorem ideleNorm_det_mul (x y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x * y)) =
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det x) *
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det y) := by
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]

private theorem siegelSet_eq_empty (w : InfinitePlace ℚ) {c C : ℝ} (hC : C < 1) : siegelSet c C = ∅ := by
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨n, t, k, -, hW⟩
  exact not_lt.mpr (one_le_of_witness w hW) hC

private theorem measure_siegelSet_inter_lt_top_of_lt_one (w : InfinitePlace ℚ) {c C : ℝ} (hC : C < 1)
    (T : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) : AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ (siegelSet c C ∩ T) < ⊤ := by
  simp [siegelSet_eq_empty w hC]

variable (w : InfinitePlace ℚ) (ι : GL (Fin 3) w.Completion →* AdelicGL 3 (𝓞 ℚ) ℚ)

private theorem ideleNorm_det_embed_eq_one (hfin : ∀ u p, componentAt3 (𝓞 ℚ) ℚ p (ι u) = 1)
    (hret : ∀ u, archPlaceComponent3 ℚ w (ι u) = u) (u : GL (Fin 3) w.Completion)
    (hu : ‖(u : Matrix (Fin 3) (Fin 3) w.Completion).det‖ = 1) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (ι u)) = 1 := by
  have hmem : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (ι u) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
    intro p
    rw [hfin u p]
    exact (localMaximalCompact3 (𝓞 ℚ) ℚ p).one_mem
  rw [ideleNorm_det_eq w hmem, hret, hu]

private theorem arch_diag_of_witness {c C : ℝ} {n t k : AdelicGL 3 (𝓞 ℚ) ℚ} (hW : IsWitness c C n t k) :
    (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) =
        Matrix.diagonal (fun i => (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i i) ∧
      (∀ i, (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i i ≠ 0) ∧
      archRoot₁ ℚ w t = ‖(archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) 0 0‖ /
          ‖(archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) 1 1‖ ∧
      archRoot₂ ℚ w t = ‖(archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) 1 1‖ /
          ‖(archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) 2 2‖ := by
  have hoff := (hW.2.2.2 w).2.1
  have hdiag := eq_diagonal_of_offDiag_eq_zero (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) hoff
  have hne := diag_entries_ne_zero w (archPlaceComponent3 ℚ w t) _ hdiag
  have h := rootSizes_of_coe_eq_diagonal (archPlaceComponent3 ℚ w t) _ hdiag (hne 1) (hne 2)
  refine ⟨hdiag, hne, ?_, ?_⟩
  · unfold archRoot₁
    exact h.1
  · unfold archRoot₂
    exact h.2

private theorem norm_det_arch_mul_eq_of_witness {c C : ℝ} {n t k : AdelicGL 3 (𝓞 ℚ) ℚ} (hW : IsWitness c C n t k) :
    ‖(archPlaceComponent3 ℚ w (n * t * k) : Matrix (Fin 3) (Fin 3) w.Completion).det‖ =
      ‖(archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion).det‖ := by
  have hbox := (hW.2.2.2 w).1
  have horth := (hW.2.2.2 w).2.2.2.2
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul,
    det_eq_one_of_unitriangular (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion)
      (fun i => (hbox i i).1) (fun i j hij => (hbox i j).2.1 hij),
    norm_one, one_mul,
    norm_det_eq_one_of_transpose_mul_eq_one (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) horth,
    mul_one]

private theorem mem_image_unipotentBox_of_witness
    (hrec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1) → ι (archPlaceComponent3 ℚ w g) = g)
    {c C : ℝ} {n t k : AdelicGL 3 (𝓞 ℚ) ℚ} (hW : IsWitness c C n t k) : n ∈ ι '' unipotentBox C := by
  have hbox := (hW.2.2.2 w).1
  refine ⟨archPlaceComponent3 ℚ w n, ?_, hrec n hW.1⟩
  refine ⟨((archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) 0 1,
    (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) 1 2,
    (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) 0 2), ?_, ?_⟩
  · exact Set.mk_mem_prod (mem_closedBall_zero_iff.2 (hbox 0 1).2.2)
      (Set.mk_mem_prod (mem_closedBall_zero_iff.2 (hbox 1 2).2.2) (mem_closedBall_zero_iff.2 (hbox 0 2).2.2))
  · exact (eq_upperUnipotent3_of_unitriangular (archPlaceComponent3 ℚ w n) (fun i => (hbox i i).1)
      (fun i j hij => (hbox i j).2.1 hij)).symm

private theorem arch_mem_rootCone_of_witness {c C : ℝ} {n t k : AdelicGL 3 (𝓞 ℚ) ℚ} (hW : IsWitness c C n t k) :
    archPlaceComponent3 ℚ w t ∈ rootCone c := by
  obtain ⟨-, hne, hroot₁, hroot₂⟩ := arch_diag_of_witness w hW
  have hc₁ := (hW.2.2.2 w).2.2.1
  have hc₂ := (hW.2.2.2 w).2.2.2.1
  rw [hroot₁] at hc₁
  rw [hroot₂] at hc₂
  refine ⟨(hW.2.2.2 w).2.1, ?_, ?_⟩
  · exact (le_div_iff₀ (norm_pos_iff.2 (hne 1))).1 hc₁
  · exact (le_div_iff₀ (norm_pos_iff.2 (hne 2))).1 hc₂

private theorem mem_image_rootCone_of_witness
    (hrec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1) → ι (archPlaceComponent3 ℚ w g) = g)
    {c C : ℝ} {n t k : AdelicGL 3 (𝓞 ℚ) ℚ} (hW : IsWitness c C n t k) : t ∈ ι '' rootCone c :=
  ⟨archPlaceComponent3 ℚ w t, arch_mem_rootCone_of_witness w hW, hrec t hW.2.1⟩

private theorem mem_image_windowSlice_of_witness
    (hrec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1) → ι (archPlaceComponent3 ℚ w g) = g)
    {c C K' a b : ℝ} {n t k : AdelicGL 3 (𝓞 ℚ) ℚ} (hW : IsWitness c C n t k) (h₁ : archRoot₁ ℚ w t ≤ K')
    (h₂ : archRoot₂ ℚ w t ≤ K')
    (hdet : ‖(archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion).det‖ ∈ Set.Icc a b) :
    t ∈ ι '' windowSlice c K' a b := by
  obtain ⟨-, hne, hroot₁, hroot₂⟩ := arch_diag_of_witness w hW
  rw [hroot₁] at h₁
  rw [hroot₂] at h₂
  refine ⟨archPlaceComponent3 ℚ w t, ⟨⟨arch_mem_rootCone_of_witness w hW, ?_, ?_⟩, hdet⟩, hrec t hW.2.1⟩
  · exact (div_le_iff₀ (norm_pos_iff.2 (hne 1))).1 h₁
  · exact (div_le_iff₀ (norm_pos_iff.2 (hne 2))).1 h₂

private theorem isWitness_of_mem (hfin : ∀ u p, componentAt3 (𝓞 ℚ) ℚ p (ι u) = 1)
    (hret : ∀ u, archPlaceComponent3 ℚ w (ι u) = u) {c C : ℝ} (hC : 1 ≤ C)
    {u t' : GL (Fin 3) w.Completion} (hu : u ∈ unipotentBox C) (ht' : t' ∈ rootCone c)
    {k : AdelicGL 3 (𝓞 ℚ) ℚ} (hk : k ∈ kSet) : IsWitness c C (ι u) (ι t') k := by
  obtain ⟨⟨x, y, z⟩, hxyz, hu_eq⟩ := hu
  have hu' : u = upperUnipotent3 x y z := hu_eq.symm
  subst hu'
  have hx : ‖x‖ ≤ C := mem_closedBall_zero_iff.1 hxyz.1
  have hy : ‖y‖ ≤ C := mem_closedBall_zero_iff.1 hxyz.2.1
  have hz : ‖z‖ ≤ C := mem_closedBall_zero_iff.1 hxyz.2.2
  have h0C : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hdiag := eq_diagonal_of_offDiag_eq_zero (t' : Matrix (Fin 3) (Fin 3) w.Completion) ht'.1
  have hne := diag_entries_ne_zero w t' _ hdiag
  have hr := rootSizes_of_coe_eq_diagonal t' _ hdiag (hne 1) (hne 2)
  refine ⟨fun p => hfin _ p, fun p => hfin _ p, hk.1, fun w' => ?_⟩
  rw [Subsingleton.elim w' w]
  unfold archRoot₁ archRoot₂
  simp only [hret]
  refine ⟨?_, ht'.1, ?_, ?_, hk.2 w⟩
  · intro i j
    rw [upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp [hx, hy, hz, hC, h0C]
  · rw [hr.1]
    exact (le_div_iff₀ (norm_pos_iff.2 (hne 1))).2 ht'.2.1
  · rw [hr.2]
    exact (le_div_iff₀ (norm_pos_iff.2 (hne 2))).2 ht'.2.2

private theorem siegelSet_eq_structuredSet (hfin : ∀ u p, componentAt3 (𝓞 ℚ) ℚ p (ι u) = 1)
    (hret : ∀ u, archPlaceComponent3 ℚ w (ι u) = u)
    (hrec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1) → ι (archPlaceComponent3 ℚ w g) = g)
    {c C : ℝ} (hC : 1 ≤ C) : siegelSet c C = structuredSet w ι c C kSet := by
  ext g
  constructor
  · rintro ⟨n, t, k, rfl, hW⟩
    unfold structuredSet
    rw [mul_assoc]
    exact Set.mul_mem_mul (mem_image_unipotentBox_of_witness w ι hrec hW)
      (Set.mul_mem_mul (mem_image_rootCone_of_witness w ι hrec hW) (mem_kSet_of_witness hW))
  · intro hg
    unfold structuredSet at hg
    obtain ⟨n, hn, tk, htk, rfl⟩ := Set.mem_mul.1 hg
    obtain ⟨t, ht, k, hk, rfl⟩ := Set.mem_mul.1 htk
    obtain ⟨u, hu, rfl⟩ := hn
    obtain ⟨t', ht', rfl⟩ := ht
    exact ⟨ι u, ι t', k, (mul_assoc _ _ _).symm, isWitness_of_mem w ι hfin hret hC hu ht' hk⟩

private theorem measurableSet_siegelSet_inter_slab (hι : Continuous ι) (hfin : ∀ u p, componentAt3 (𝓞 ℚ) ℚ p (ι u) = 1)
    (hret : ∀ u, archPlaceComponent3 ℚ w (ι u) = u)
    (hrec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1) → ι (archPlaceComponent3 ℚ w g) = g)
    (hK : IsCompact kSet) (c C a b : ℝ) :
    @MeasurableSet _ (AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ)
      (siegelSet c C ∩ {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) := by
  letI := AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  rw [siegelSet_inter_slab_eq w]
  by_cases hC : 1 ≤ C
  · rw [siegelSet_eq_structuredSet w ι hfin hret hrec hC]
    exact ((isClosed_structuredSet w ι hι hfin hret hrec c C hK).inter
      (isClosed_setOf_norm_det_mem_Icc w (continuous_archPlaceComponent3 w) a b)).measurableSet
  · rw [siegelSet_eq_empty w (not_le.1 hC), Set.empty_inter]
    exact MeasurableSet.empty

private def windowBlock (c C K' a b : ℝ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  ι '' unipotentBox C * (ι '' windowSlice c K' a b * kSet)

private theorem isCompact_windowBlock (hι : Continuous ι) (hK : IsCompact kSet) {c K' a : ℝ} (hc : 0 < c)
    (hK' : 0 < K')
    (ha : 0 < a) (C b : ℝ) : IsCompact (windowBlock w ι c C K' a b) := by
  haveI : ProperSpace w.Completion := AutomorphicForm.WindowedSiegel.properSpace_completion w
  have hbox : IsCompact (ι '' unipotentBox C) := (isCompact_unipotentBox C).image hι
  have hslice : IsCompact (ι '' windowSlice c K' a b) := (isCompact_windowSlice hc hK' ha b).image hι
  unfold windowBlock
  exact hbox.mul (hslice.mul hK)

private theorem measure_windowBlock_lt_top (hι : Continuous ι) (hK : IsCompact kSet) {c K' a : ℝ} (hc : 0 < c)
    (hK' : 0 < K') (ha : 0 < a) (C b : ℝ) :
    AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ (windowBlock w ι c C K' a b) < ⊤ := by
  letI := AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  exact (isCompact_windowBlock w ι hι hK hc hK' ha C b).measure_lt_top

private theorem mem_windowBlock_of_mem
    (hrec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1) → ι (archPlaceComponent3 ℚ w g) = g)
    {c C : ℝ}
    (hroot : ∀ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, IsWitness c C n t k →
      archRoot₁ ℚ w (n * t * k) = archRoot₁ ℚ w t ∧ archRoot₂ ℚ w (n * t * k) = archRoot₂ ℚ w t)
    {K' a b : ℝ} {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : g ∈ siegelSet c C)
    (hslab : NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b)
    (h₁ : archRoot₁ ℚ w g ≤ K') (h₂ : archRoot₂ ℚ w g ≤ K') : g ∈ windowBlock w ι c C K' a b := by
  have hkp := mem_localMaximalCompact3_of_mem_siegelSet hg
  obtain ⟨n, t, k, rfl, hW⟩ := hg
  rw [(hroot n t k hW).1] at h₁
  rw [(hroot n t k hW).2] at h₂
  rw [ideleNorm_det_eq w hkp, norm_det_arch_mul_eq_of_witness w hW] at hslab
  unfold windowBlock
  rw [mul_assoc]
  exact Set.mul_mem_mul (mem_image_unipotentBox_of_witness w ι hrec hW)
    (Set.mul_mem_mul (mem_image_windowSlice_of_witness w ι hrec hW h₁ h₂ hslab) (mem_kSet_of_witness hW))

private theorem measure_siegelSet_inter_slab_inter_caps_lt_top (hι : Continuous ι)
    (hrec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1) → ι (archPlaceComponent3 ℚ w g) = g)
    (hK : IsCompact kSet) {c C : ℝ}
    (hroot : ∀ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, IsWitness c C n t k →
      archRoot₁ ℚ w (n * t * k) = archRoot₁ ℚ w t ∧ archRoot₂ ℚ w (n * t * k) = archRoot₂ ℚ w t)
    (hc : 0 < c) {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
      (siegelSet c C ∩ {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} ∩
        archRoot₁ ℚ w ⁻¹' Set.Iio (r * c) ∩ archRoot₂ ℚ w ⁻¹' Set.Iio (r * c)) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono ?_) (measure_windowBlock_lt_top w ι hι hK hc (mul_pos hr hc) ha C b)
  rintro g ⟨⟨⟨hg, hslab⟩, h₁⟩, h₂⟩
  have h₁' : archRoot₁ ℚ w g < r * c := h₁
  have h₂' : archRoot₂ ℚ w g < r * c := h₂
  exact mem_windowBlock_of_mem w ι hrec hroot hg hslab h₁'.le h₂'.le

end Adelic

end SiegelSetBlock

end

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.LanglandsTunnell.CubicInduction"
open SiegelContraction SiegelSetTopology

noncomputable section

namespace SiegelSetBlock

section KBridge

private theorem isClosed_localMaximalCompact3 (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsClosed (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (GL (Fin 3) (p.adicCompletion ℚ))) := by
  have h : (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (GL (Fin 3) (p.adicCompletion ℚ))) =
      (⋂ i : Fin 3, ⋂ j : Fin 3,
        (fun k : GL (Fin 3) (p.adicCompletion ℚ) => (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ⁻¹'
          (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) ∩
      ⋂ i : Fin 3, ⋂ j : Fin 3,
        (fun k : GL (Fin 3) (p.adicCompletion ℚ) =>
          ((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ⁻¹'
          (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
    ext k
    simp only [SetLike.mem_coe, mem_localMaximalCompact3_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [h]
  refine (isClosed_iInter fun i => isClosed_iInter fun j => ?_).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
  · exact (AdelicLevel.isClosed_adicCompletionIntegers (K := ℚ) p).preimage (Units.continuous_val.matrix_elem i j)
  · exact (AdelicLevel.isClosed_adicCompletionIntegers (K := ℚ) p).preimage
      (Units.continuous_coe_inv.matrix_elem i j)

private theorem continuous_componentAt3 (p : HeightOneSpectrum (𝓞 ℚ)) : Continuous (componentAt3 (𝓞 ℚ) ℚ p) := by
  unfold componentAt3 componentAtN
  exact continuous_glMap3 _
    ((AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.continuous_adeleFin (R := 𝓞 ℚ) (K := ℚ)))

private theorem isClosed_kSet : IsClosed kSet := by
  have h : kSet =
      (⋂ p : HeightOneSpectrum (𝓞 ℚ), (componentAt3 (𝓞 ℚ) ℚ p) ⁻¹'
        (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (GL (Fin 3) (p.adicCompletion ℚ)))) ∩
      ⋂ w : InfinitePlace ℚ, {k : AdelicGL 3 (𝓞 ℚ) ℚ |
        (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1} := by
    ext k
    simp only [kSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [h]
  refine (isClosed_iInter fun p => (isClosed_localMaximalCompact3 p).preimage (continuous_componentAt3 p)).inter
    (isClosed_iInter fun w => ?_)
  have hA : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      (archPlaceComponent3 ℚ w g : Matrix (Fin 3) (Fin 3) w.Completion) :=
    Units.continuous_val.comp (continuous_archPlaceComponent3 w)
  exact isClosed_eq (hA.matrix_transpose.matrix_mul hA) continuous_const

private theorem norm_entry_le_one_of_transpose_mul_eq_one (w₀ : InfinitePlace ℚ) (e : w₀.Completion ≃+* ℝ)
    (he : ∀ r : ℝ, ‖e.symm r‖ = ‖r‖) (M : GL (Fin 3) w₀.Completion)
    (hM : (M : Matrix (Fin 3) (Fin 3) w₀.Completion)ᵀ * (M : Matrix (Fin 3) (Fin 3) w₀.Completion) = 1)
    (i j : Fin 3) : ‖(M : Matrix (Fin 3) (Fin 3) w₀.Completion) i j‖ ≤ 1 := by
  have hR := toRealPlace_orthogonal w₀ e M hM
  rw [norm_eq_abs_apply w₀ e he, ← toRealPlace_apply w₀ e M i j]
  set N : Matrix (Fin 3) (Fin 3) ℝ := ((toRealPlace w₀ e M : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
  have hjj := congrFun (congrFun hR j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hjj
  simp only [Matrix.transpose_apply] at hjj
  have hle : N i j * N i j ≤ ∑ i' : Fin 3, N i' j * N i' j :=
    Finset.single_le_sum (fun i' _ => mul_self_nonneg (N i' j)) (Finset.mem_univ i)
  refine (sq_le_one_iff₀ (abs_nonneg _)).mp ?_
  rw [sq, abs_mul_abs_self]
  exact hle.trans hjj.le

private theorem kSet_subset_unitEntryMatrices (w₀ : InfinitePlace ℚ) (e : w₀.Completion ≃+* ℝ)
    (he : ∀ r : ℝ, ‖e.symm r‖ = ‖r‖) : kSet ⊆ unitEntryMatrices := by
  intro k hk
  obtain ⟨hfin, horth⟩ := hk
  refine mem_unitEntryMatrices hfin (fun w i j => ?_) (fun w i j => ?_)
  · rw [Subsingleton.elim w w₀]
    exact norm_entry_le_one_of_transpose_mul_eq_one w₀ e he _ (horth w₀) i j
  · rw [Subsingleton.elim w w₀, map_inv, Units.inv_eq_of_mul_eq_one_left (horth w₀), Matrix.transpose_apply]
    exact norm_entry_le_one_of_transpose_mul_eq_one w₀ e he _ (horth w₀) j i

private theorem isCompact_kSet (w₀ : InfinitePlace ℚ) (e : w₀.Completion ≃+* ℝ) (he : ∀ r : ℝ, ‖e.symm r‖ = ‖r‖) :
    IsCompact kSet :=
  isCompact_unitEntryMatrices.of_isClosed_subset isClosed_kSet (kSet_subset_unitEntryMatrices w₀ e he)

end KBridge

end SiegelSetBlock

end

set_option autoImplicit false

p2m_open "Matrix NumberField NumberField.AdelicLevel IsDedekindDomain LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.LanglandsTunnell.CubicInduction"

noncomputable section

namespace SiegelArchEmbed

variable (F : Type) [Field F]

open scoped Classical in
private def archPiMat3 (v₀ : InfinitePlace F) (g : Matrix (Fin 3) (Fin 3) v₀.Completion) :
    Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F) :=
  Matrix.of fun i j =>
    (Function.update ((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F)) i j) v₀ (g i j) : InfiniteAdeleRing F)

private theorem matrix_eq_of_forall_archEval {M N : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, (archEval F w).mapMatrix M = (archEval F w).mapMatrix N) : M = N := by
  refine Matrix.ext fun i j => funext fun w => ?_
  have hw := congrFun (congrFun (h w) i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, archEval_apply] using hw

open scoped Classical in
private theorem archEval_mapMatrix_archPiMat3_self (v₀ : InfinitePlace F) (g : Matrix (Fin 3) (Fin 3) v₀.Completion) :
    (archEval F v₀).mapMatrix (archPiMat3 F v₀ g) = g := by
  ext i j
  simp [archPiMat3, archEval_apply]

open scoped Classical in
private theorem archEval_mapMatrix_archPiMat3_of_ne (v₀ : InfinitePlace F) (g : Matrix (Fin 3) (Fin 3) v₀.Completion)
    {w : InfinitePlace F} (hw : w ≠ v₀) : (archEval F w).mapMatrix (archPiMat3 F v₀ g) = 1 := by
  ext i j
  simp only [archPiMat3, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, archEval_apply,
    Function.update_of_ne hw]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]
    rfl

private theorem archPiMat3_one (v₀ : InfinitePlace F) : archPiMat3 F v₀ 1 = 1 :=
  matrix_eq_of_forall_archEval F fun w => by
    by_cases hw : w = v₀
    · subst hw
      rw [archEval_mapMatrix_archPiMat3_self, map_one]
    · rw [archEval_mapMatrix_archPiMat3_of_ne F _ _ hw, map_one]

private theorem archPiMat3_mul (v₀ : InfinitePlace F) (g h : Matrix (Fin 3) (Fin 3) v₀.Completion) :
    archPiMat3 F v₀ (g * h) = archPiMat3 F v₀ g * archPiMat3 F v₀ h :=
  matrix_eq_of_forall_archEval F fun w => by
    by_cases hw : w = v₀
    · subst hw
      rw [map_mul, archEval_mapMatrix_archPiMat3_self, archEval_mapMatrix_archPiMat3_self,
        archEval_mapMatrix_archPiMat3_self]
    · rw [map_mul, archEval_mapMatrix_archPiMat3_of_ne F _ _ hw, archEval_mapMatrix_archPiMat3_of_ne F _ _ hw,
        archEval_mapMatrix_archPiMat3_of_ne F _ _ hw, mul_one]

variable [NumberField F]

private def infMat3 (M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    ((M i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F)

private theorem matrix_eq_of_arch_fin {M N : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F)}
    (h₁ : (adeleArch (𝓞 F) F).mapMatrix M = (adeleArch (𝓞 F) F).mapMatrix N)
    (h₂ : (adeleFin (𝓞 F) F).mapMatrix M = (adeleFin (𝓞 F) F).mapMatrix N) : M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply, adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

private theorem adeleArch_mapMatrix_infMat3 (M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F)) :
    (adeleArch (𝓞 F) F).mapMatrix (infMat3 F M) = M := by
  ext i j
  simp [infMat3, adeleArch_apply]

private theorem adeleFin_mapMatrix_infMat3 (M : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F)) :
    (adeleFin (𝓞 F) F).mapMatrix (infMat3 F M) = 1 := by
  ext i j
  simp [infMat3, adeleFin_apply]

private theorem infMat3_one : infMat3 F 1 = 1 :=
  matrix_eq_of_arch_fin F (by rw [adeleArch_mapMatrix_infMat3, map_one])
    (by rw [adeleFin_mapMatrix_infMat3, map_one])

private theorem infMat3_mul (M N : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing F)) :
    infMat3 F (M * N) = infMat3 F M * infMat3 F N :=
  matrix_eq_of_arch_fin F
    (by rw [map_mul, adeleArch_mapMatrix_infMat3, adeleArch_mapMatrix_infMat3, adeleArch_mapMatrix_infMat3])
    (by rw [map_mul, adeleFin_mapMatrix_infMat3, adeleFin_mapMatrix_infMat3, adeleFin_mapMatrix_infMat3, mul_one])

private def archEmbed3 (v₀ : InfinitePlace F) : GL (Fin 3) v₀.Completion →* AdelicGL 3 (𝓞 F) F where
  toFun g :=
    { val := infMat3 F (archPiMat3 F v₀ g)
      inv := infMat3 F (archPiMat3 F v₀ ((g⁻¹ : GL (Fin 3) v₀.Completion) : Matrix _ _ _))
      val_inv := by rw [← infMat3_mul, ← archPiMat3_mul, Units.mul_inv, archPiMat3_one, infMat3_one]
      inv_val := by rw [← infMat3_mul, ← archPiMat3_mul, Units.inv_mul, archPiMat3_one, infMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; rw [archPiMat3_one, infMat3_one])
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; rw [archPiMat3_mul, infMat3_mul])

private theorem coe_archEmbed3 (v₀ : InfinitePlace F) (g : GL (Fin 3) v₀.Completion) :
    (archEmbed3 F v₀ g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 F) F)) = infMat3 F (archPiMat3 F v₀ g) := rfl

variable {F}

private theorem componentAt3_archEmbed3 (v₀ : InfinitePlace F) (p : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin 3) v₀.Completion) :
    componentAt3 (𝓞 F) F p (archEmbed3 F v₀ g) = 1 :=
  Units.ext (by
    show (finAdeleEval (𝓞 F) F p).mapMatrix ((adeleFin (𝓞 F) F).mapMatrix (infMat3 F (archPiMat3 F v₀ g))) = 1
    rw [adeleFin_mapMatrix_infMat3, map_one])

private theorem archPlaceComponent3_archEmbed3_self (v₀ : InfinitePlace F) (g : GL (Fin 3) v₀.Completion) :
    archPlaceComponent3 F v₀ (archEmbed3 F v₀ g) = g :=
  Units.ext (by
    show (archEval F v₀).mapMatrix ((adeleArch (𝓞 F) F).mapMatrix (infMat3 F (archPiMat3 F v₀ g))) = g
    rw [adeleArch_mapMatrix_infMat3, archEval_mapMatrix_archPiMat3_self])

private theorem archPlaceComponent3_archEmbed3_of_ne (v₀ : InfinitePlace F) (g : GL (Fin 3) v₀.Completion)
    {w : InfinitePlace F} (hw : w ≠ v₀) : archPlaceComponent3 F w (archEmbed3 F v₀ g) = 1 :=
  Units.ext (by
    show (archEval F w).mapMatrix ((adeleArch (𝓞 F) F).mapMatrix (infMat3 F (archPiMat3 F v₀ g))) = 1
    rw [adeleArch_mapMatrix_infMat3, archEval_mapMatrix_archPiMat3_of_ne F _ _ hw])

private theorem archPlaceComponent3_archEmbed3_mul (w : InfinitePlace F) (s : GL (Fin 3) w.Completion)
    (g : AdelicGL 3 (𝓞 F) F) :
    archPlaceComponent3 F w (archEmbed3 F w s * g) = s * archPlaceComponent3 F w g := by
  rw [map_mul, archPlaceComponent3_archEmbed3_self]

private theorem componentAt3_archEmbed3_mul (v₀ : InfinitePlace F) (p : HeightOneSpectrum (𝓞 F))
    (s : GL (Fin 3) v₀.Completion) (g : AdelicGL 3 (𝓞 F) F) :
    componentAt3 (𝓞 F) F p (archEmbed3 F v₀ s * g) = componentAt3 (𝓞 F) F p g := by
  rw [map_mul, componentAt3_archEmbed3, one_mul]

private theorem componentAt3_globalPointsGL (p : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin 3) F) :
    componentAt3 (𝓞 F) F p (globalPointsGL 3 (𝓞 F) F γ) =
      Matrix.GeneralLinearGroup.map (algebraMap F (p.adicCompletion F)) γ :=
  Units.ext (by ext i j; rfl)

private theorem componentAt3_globalPointsGL_mul (p : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin 3) F)
    (g : AdelicGL 3 (𝓞 F) F) :
    componentAt3 (𝓞 F) F p (globalPointsGL 3 (𝓞 F) F γ * g) =
      Matrix.GeneralLinearGroup.map (algebraMap F (p.adicCompletion F)) γ * componentAt3 (𝓞 F) F p g := by
  rw [map_mul, componentAt3_globalPointsGL]

private theorem archPlaceComponent3_globalPointsGL (w : InfinitePlace F) (γ : GL (Fin 3) F) :
    archPlaceComponent3 F w (globalPointsGL 3 (𝓞 F) F γ) =
      Matrix.GeneralLinearGroup.map (algebraMap F w.Completion) γ :=
  Units.ext (by ext i j; rfl)

private theorem archPlaceComponent3_globalPointsGL_mul (w : InfinitePlace F) (γ : GL (Fin 3) F)
    (g : AdelicGL 3 (𝓞 F) F) :
    archPlaceComponent3 F w (globalPointsGL 3 (𝓞 F) F γ * g) =
      Matrix.GeneralLinearGroup.map (algebraMap F w.Completion) γ * archPlaceComponent3 F w g := by
  rw [map_mul, archPlaceComponent3_globalPointsGL]

open scoped Classical in
private theorem continuous_infMat3_archPiMat3 (v₀ : InfinitePlace F) :
    Continuous fun M : Matrix (Fin 3) (Fin 3) v₀.Completion => infMat3 F (archPiMat3 F v₀ M) := by
  refine continuous_matrix fun i j => ?_
  simp only [infMat3, archPiMat3, Matrix.of_apply]
  refine Continuous.prodMk ?_ continuous_const
  refine continuous_pi fun w => ?_
  by_cases hw : w = v₀
  · subst hw
    simp only [Function.update_self]
    exact continuous_id.matrix_elem i j
  · simp only [Function.update_of_ne hw]
    exact continuous_const

private theorem continuous_archEmbed3 (v₀ : InfinitePlace F) : Continuous (archEmbed3 F v₀) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_infMat3_archPiMat3 v₀).comp Units.continuous_val
  · exact (continuous_infMat3_archPiMat3 v₀).comp Units.continuous_coe_inv

section Rat

private theorem finiteAdele_ext {x y : FiniteAdeleRing (𝓞 ℚ) ℚ}
    (h : ∀ p : HeightOneSpectrum (𝓞 ℚ), finAdeleEval (𝓞 ℚ) ℚ p x = finAdeleEval (𝓞 ℚ) ℚ p y) : x = y := by
  ext p
  simpa only [finAdeleEval_apply] using h p

private theorem adeleFin_mapMatrix_eq_one_of_forall_componentAt3 {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p g = 1) :
    (adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
  refine Matrix.ext fun i j => ?_
  refine finiteAdele_ext fun p => ?_
  have hp0 := congrArg Units.val (hg p)
  have hp : (finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix
      ((adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := hp0
  have hp' := congrFun (congrFun hp i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hp'
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [hp']
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]

private theorem archEmbed3_archPlaceComponent3_of_forall_componentAt3 (w : InfinitePlace ℚ) {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p g = 1) :
    archEmbed3 ℚ w (archPlaceComponent3 ℚ w g) = g := by
  refine Units.ext ?_
  rw [coe_archEmbed3]
  refine matrix_eq_of_arch_fin ℚ ?_ ?_
  · rw [adeleArch_mapMatrix_infMat3]
    refine matrix_eq_of_forall_archEval ℚ fun w' => ?_
    rw [Subsingleton.elim w' w, archEval_mapMatrix_archPiMat3_self]
    rfl
  · rw [adeleFin_mapMatrix_infMat3, adeleFin_mapMatrix_eq_one_of_forall_componentAt3 hg]

end Rat

end SiegelArchEmbed

end

set_option autoImplicit false

open Matrix NumberField

noncomputable section

namespace SiegelRealTransport

private def RealReduction : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ M : GL (Fin 3) ℝ,
    ∃ (γ : GL (Fin 3) ℤ) (n t k : GL (Fin 3) ℝ),
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ * M = n * t * k ∧
      (∀ i j : Fin 3,
        (n : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 ∧ (j < i → (n : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
        ‖(n : Matrix (Fin 3) (Fin 3) ℝ) i j‖ ≤ C) ∧
      (∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
      (∀ i : Fin 3, 0 < (t : Matrix (Fin 3) (Fin 3) ℝ) i i) ∧
      c ≤ (t : Matrix (Fin 3) (Fin 3) ℝ) 0 0 / (t : Matrix (Fin 3) (Fin 3) ℝ) 1 1 ∧
      c ≤ (t : Matrix (Fin 3) (Fin 3) ℝ) 1 1 / (t : Matrix (Fin 3) (Fin 3) ℝ) 2 2 ∧
      (k : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (k : Matrix (Fin 3) (Fin 3) ℝ) = 1

section Functor

variable {A B : Type*} [CommRing A] [CommRing B]

private theorem coe_map (f : A →+* B) (g : GL (Fin 3) A) (i j : Fin 3) :
    (Matrix.GeneralLinearGroup.map f g : Matrix (Fin 3) (Fin 3) B) i j = f ((g : Matrix (Fin 3) (Fin 3) A) i j) :=
  rfl

private theorem map_symm_map (e : A ≃+* B) (g : GL (Fin 3) A) :
    Matrix.GeneralLinearGroup.map (e.symm : B →+* A) (Matrix.GeneralLinearGroup.map (e : A →+* B) g) = g :=
  Units.ext (by ext i j; simp)

private theorem map_symm_map_intCast (e : A ≃+* B) (γ : GL (Fin 3) ℤ) :
    Matrix.GeneralLinearGroup.map (e.symm : B →+* A) (Matrix.GeneralLinearGroup.map (Int.castRingHom B) γ) =
      Matrix.GeneralLinearGroup.map (Int.castRingHom A) γ :=
  Units.ext (by ext i j; simp)

private theorem transpose_mul_map_eq_one (f : A →+* B) {k : Matrix (Fin 3) (Fin 3) A} (hk : kᵀ * k = 1) :
    (k.map f)ᵀ * k.map f = 1 := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul, hk, Matrix.map_one f (map_zero f) (map_one f)]

private theorem map_intCast_eq_map_algebraMap {L : Type*} [Field L] [Algebra ℚ L] (γ : GL (Fin 3) ℤ) :
    Matrix.GeneralLinearGroup.map (Int.castRingHom L) γ =
      Matrix.GeneralLinearGroup.map (algebraMap ℚ L) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) γ) :=
  Units.ext (by ext i j; simp)

end Functor

section RealPlace

variable {K : Type*} [Field K]

private theorem norm_symm_ringEquivRealOfIsReal {w : InfinitePlace K} (hw : w.IsReal) (x : ℝ) :
    ‖(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)
    ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x)
  rw [← h]
  congr 1
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal hw).apply_symm_apply x

private theorem exists_reduced_of_isReal (hRB : RealReduction) :
    ∃ c C : ℝ, 0 < c ∧ ∀ (w : InfinitePlace K) (_hw : w.IsReal) (M : GL (Fin 3) w.Completion),
      ∃ (γ : GL (Fin 3) ℤ) (n t k : GL (Fin 3) w.Completion),
        Matrix.GeneralLinearGroup.map (Int.castRingHom w.Completion) γ * M = n * t * k ∧
        (∀ i j : Fin 3,
          (n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
          (j < i → (n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          ‖(n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
        (∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
        c ≤ ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 0 0‖ / ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 1 1‖ ∧
        c ≤ ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 1 1‖ / ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 2 2‖ ∧
        (k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ * (k : Matrix (Fin 3) (Fin 3) w.Completion) = 1 := by
  obtain ⟨c, C, hc, hred⟩ := hRB
  refine ⟨c, C, hc, fun w hw M => ?_⟩
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he
  obtain ⟨γ, n, t, k, hprod, hn, htd, htpos, hr1, hr2, hk⟩ := hred (Matrix.GeneralLinearGroup.map (e : _ →+* ℝ) M)
  have hnorm : ∀ x : ℝ, ‖e.symm x‖ = ‖x‖ := norm_symm_ringEquivRealOfIsReal hw
  have hnorm' : ∀ x : ℝ, ‖(e.symm : ℝ →+* w.Completion) x‖ = ‖x‖ := hnorm
  refine ⟨γ,
    Matrix.GeneralLinearGroup.map (e.symm : ℝ →+* w.Completion) n,
    Matrix.GeneralLinearGroup.map (e.symm : ℝ →+* w.Completion) t,
    Matrix.GeneralLinearGroup.map (e.symm : ℝ →+* w.Completion) k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h := congrArg (Matrix.GeneralLinearGroup.map (e.symm : ℝ →+* w.Completion)) hprod
    rwa [map_mul, map_mul, map_mul, map_symm_map, map_symm_map_intCast] at h
  · intro i j
    obtain ⟨h1, h0, hC⟩ := hn i j
    refine ⟨?_, fun hji => ?_, ?_⟩
    · rw [coe_map, h1, map_one]
    · rw [coe_map, h0 hji, map_zero]
    · rw [coe_map, hnorm']
      exact hC
  · intro i j hij
    rw [coe_map, htd i j hij, map_zero]
  · rw [coe_map, coe_map, hnorm', hnorm', Real.norm_of_nonneg (htpos 0).le, Real.norm_of_nonneg (htpos 1).le]
    exact hr1
  · rw [coe_map, coe_map, hnorm', hnorm', Real.norm_of_nonneg (htpos 1).le, Real.norm_of_nonneg (htpos 2).le]
    exact hr2
  · exact transpose_mul_map_eq_one (e.symm : ℝ →+* w.Completion) hk

end RealPlace

private theorem isReal_of_rat (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

private theorem exists_reduced_rat (hRB : RealReduction) :
    ∃ c C : ℝ, 0 < c ∧ ∀ (w : InfinitePlace ℚ) (M : GL (Fin 3) w.Completion),
      ∃ (γ : GL (Fin 3) ℤ) (n t k : GL (Fin 3) w.Completion),
        Matrix.GeneralLinearGroup.map (Int.castRingHom w.Completion) γ * M = n * t * k ∧
        (∀ i j : Fin 3,
          (n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
          (j < i → (n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          ‖(n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
        (∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
        c ≤ ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 0 0‖ / ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 1 1‖ ∧
        c ≤ ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 1 1‖ / ‖(t : Matrix (Fin 3) (Fin 3) w.Completion) 2 2‖ ∧
        (k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ * (k : Matrix (Fin 3) (Fin 3) w.Completion) = 1 := by
  obtain ⟨c, C, hc, h⟩ := exists_reduced_of_isReal (K := ℚ) hRB
  exact ⟨c, C, hc, fun w M => h w (isReal_of_rat w) M⟩

end SiegelRealTransport

end

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.SiegelContraction P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.SiegelSetBlock P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.SiegelSetTopology"

noncomputable section

namespace SiegelAssembly

private def slabSet (a b : ℝ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

variable (w₀ : InfinitePlace ℚ) (e : w₀.Completion ≃+* ℝ) (he : ∀ r : ℝ, ‖e.symm r‖ = ‖r‖)
  (ι : GL (Fin 3) w₀.Completion →* AdelicGL 3 (𝓞 ℚ) ℚ) (hι : Continuous ι)
  (hw : ∀ w : InfinitePlace ℚ, w = w₀)
  (hfin : ∀ (u : GL (Fin 3) w₀.Completion) (p : HeightOneSpectrum (𝓞 ℚ)), componentAt3 (𝓞 ℚ) ℚ p (ι u) = 1)
  (hret : ∀ u : GL (Fin 3) w₀.Completion, archPlaceComponent3 ℚ w₀ (ι u) = u)
  (hrec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p, componentAt3 (𝓞 ℚ) ℚ p g = 1) → ι (archPlaceComponent3 ℚ w₀ g) = g)

include he hι hw hfin hret hrec in

private theorem siegelSet_inter_slab_lt_top (c C : ℝ) (hc : 0 < c) (a b : ℝ) (ha : 0 < a) :
    AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
      (siegelSet c C ∩ slabSet a b) < ⊤ := by
  by_cases hC : C < 1
  · exact measure_siegelSet_inter_lt_top_of_lt_one w₀ hC _
  have hC1 : (1 : ℝ) ≤ C := not_lt.mp hC
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  have hρ : ∀ q : ℚ, ‖algebraMap ℚ w₀.Completion q‖ = |q| := norm_algebraMap_rat w₀ e he
  have hK : IsCompact kSet := isCompact_kSet w₀ e he
  have hone : ∀ u : GL (Fin 3) w₀.Completion, ‖(u : Matrix (Fin 3) (Fin 3) w₀.Completion).det‖ = 1 →
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (ι u)) = 1 :=
    fun u hu => ideleNorm_det_embed_eq_one w₀ ι hfin hret u hu
  have hroot : ∀ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, IsWitness c C n t k →
      archRoot₁ ℚ w₀ (n * t * k) = archRoot₁ ℚ w₀ t ∧ archRoot₂ ℚ w₀ (n * t * k) = archRoot₂ ℚ w₀ t :=
    fun n t k hW => archRoot_mul_eq_of_witness w₀ e he hW
  have h14 : (1 / 4 : ℚ) ≠ 0 := by norm_num
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have h12 : (1 / 2 : ℚ) ≠ 0 := by norm_num
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  have st1 := stage_one_ratios
  have st2 := stage_two_ratios
  have c18 : ((|(1 / 4 : ℚ) / 2| : ℚ) : ℝ) = 1 / 8 := by rw [st1.2.2.1]; norm_num
  have c1 : ((|(2 : ℚ) / 2| : ℚ) : ℝ) = 1 := by rw [st1.2.2.2.1]; norm_num
  have d1 : ((|(1 / 2 : ℚ) / (1 / 2)| : ℚ) : ℝ) = 1 := by rw [st2.2.2.1]; norm_num
  have d18 : ((|(1 / 2 : ℚ) / 4| : ℚ) : ℝ) = 1 / 8 := by rw [st2.2.2.2.1]; norm_num
  obtain ⟨s₁, hs₁, hsep₁⟩ := exists_shear ((1 / 4 : ℚ) / 2) st1.2.2.1 hC1
  obtain ⟨s₂, hs₂, hsep₂⟩ := exists_shear ((1 / 2 : ℚ) / 4) st2.2.2.2.1 hC1
  have hr8 : (1 : ℝ) < 8 := by norm_num
  set S₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
    siegelSet c C ∩ slabSet a b with hS₀_def
  have hS₀ : MeasurableSet S₀ := measurableSet_siegelSet_inter_slab w₀ ι hι hfin hret hrec hK c C a b
  have hwin : ∀ (x y z : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0), |x * y * z| = 1 →
      ∀ (s : ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), g ∈ S₀ → deviceElt w₀ ι x y z hx hy hz s * g ∈ slabSet a b := by
    intro x y z hx hy hz hdet s g hg
    show NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (deviceElt w₀ ι x y z hx hy hz s * g)) ∈
      Set.Icc a b
    rw [ideleNorm_det_deviceElt_mul w₀ ι ideleNorm_det_mul hone hρ x y z hx hy hz hdet s g]
    exact hg.2
  refine MeasureTheory.ContractionDecay.measure_lt_top_of_measure_inter_lt_top _ hS₀ (measurable_archRoot₁ w₀) hc hr8
    (fun g hg => (le_archRoot_of_mem w₀ e he hg.1).1)
    (p := deviceElt w₀ ι (1 / 4) 2 2 h14 h2 h2 s₁) (q := deviceElt w₀ ι (1 / 4) 2 2 h14 h2 h2 (-s₁)) ?_ ?_ ?_ ?_
  · intro g hg h8
    obtain ⟨hmem, hr₁, -⟩ := deviceElt_mul_mem w₀ e he ι hw hfin hret (1 / 4) 2 2 h14 h2 h2 s₁ st1.1 st1.2.1 hs₁ hg.1
      (by rw [c18]; linarith) (by rw [c1, one_mul]; exact (le_archRoot_of_mem w₀ e he hg.1).2)
    refine ⟨⟨hmem, hwin _ _ _ _ _ _ st1.2.2.2.2 s₁ g hg⟩, ?_⟩
    rw [hr₁, c18]
    ring
  · intro g hg h8
    obtain ⟨hmem, hr₁, -⟩ := deviceElt_mul_mem w₀ e he ι hw hfin hret (1 / 4) 2 2 h14 h2 h2 (-s₁) st1.1 st1.2.1
      (by rw [abs_neg]; exact hs₁) hg.1
      (by rw [c18]; linarith) (by rw [c1, one_mul]; exact (le_archRoot_of_mem w₀ e he hg.1).2)
    refine ⟨⟨hmem, hwin _ _ _ _ _ _ st1.2.2.2.2 (-s₁) g hg⟩, ?_⟩
    rw [hr₁, c18]
    ring
  · intro g hg g' hg' _ _
    exact deviceElt_mul_ne w₀ e he ι hret (1 / 4) 2 2 h14 h2 h2 s₁ (-s₁) hsep₁ hg.1 hg'.1
  set S₁ : Set (AdelicGL 3 (𝓞 ℚ) ℚ) := S₀ ∩ archRoot₁ ℚ w₀ ⁻¹' Set.Iio (8 * c) with hS₁_def
  have hS₁ : MeasurableSet S₁ := hS₀.inter (measurable_archRoot₁ w₀ measurableSet_Iio)
  refine MeasureTheory.ContractionDecay.measure_lt_top_of_measure_inter_lt_top _ hS₁ (measurable_archRoot₂ w₀) hc hr8
    (fun g hg => (le_archRoot_of_mem w₀ e he hg.1.1).2)
    (p := deviceElt w₀ ι (1 / 2) (1 / 2) 4 h12 h12 h4 s₂) (q := deviceElt w₀ ι (1 / 2) (1 / 2) 4 h12 h12 h4 (-s₂))
    ?_ ?_ ?_ ?_
  · intro g hg h8
    obtain ⟨hmem, hr₁, hr₂⟩ := deviceElt_mul_mem w₀ e he ι hw hfin hret (1 / 2) (1 / 2) 4 h12 h12 h4 s₂ st2.1 st2.2.1
      hs₂ hg.1.1 (by rw [d1, one_mul]; exact (le_archRoot_of_mem w₀ e he hg.1.1).1) (by rw [d18]; linarith)
    refine ⟨⟨⟨hmem, hwin _ _ _ _ _ _ st2.2.2.2.2 s₂ g hg.1⟩, ?_⟩, ?_⟩
    · show archRoot₁ ℚ w₀ _ < 8 * c
      rw [hr₁, d1, one_mul]
      exact hg.2
    · rw [hr₂, d18]
      ring
  · intro g hg h8
    obtain ⟨hmem, hr₁, hr₂⟩ := deviceElt_mul_mem w₀ e he ι hw hfin hret (1 / 2) (1 / 2) 4 h12 h12 h4 (-s₂) st2.1
      st2.2.1 (by rw [abs_neg]; exact hs₂) hg.1.1
      (by rw [d1, one_mul]; exact (le_archRoot_of_mem w₀ e he hg.1.1).1) (by rw [d18]; linarith)
    refine ⟨⟨⟨hmem, hwin _ _ _ _ _ _ st2.2.2.2.2 (-s₂) g hg.1⟩, ?_⟩, ?_⟩
    · show archRoot₁ ℚ w₀ _ < 8 * c
      rw [hr₁, d1, one_mul]
      exact hg.2
    · rw [hr₂, d18]
      ring
  · intro g hg g' hg' _ _
    exact deviceElt_mul_ne w₀ e he ι hret (1 / 2) (1 / 2) 4 h12 h12 h4 s₂ (-s₂) hsep₂ hg.1.1 hg'.1.1
  · exact measure_siegelSet_inter_slab_inter_caps_lt_top w₀ ι hι hrec hK hroot hc (by norm_num : (0 : ℝ) < 8) ha b

include he hι hw hfin hret hrec in

private theorem slab_lt_top_k1_shape
    (c C : ℝ) (_hc : 0 < c) (a b : ℝ) (_ha : 0 < a) (_hab : a < b) :
    NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
        ({g : AdelicGL 3 (𝓞 ℚ) ℚ | ∃ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, g = n * t * k ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
          ∀ w : InfinitePlace ℚ,
            (∀ i j : Fin 3,
              (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
              (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
              ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
            (∀ i j : Fin 3, i ≠ j →
              (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
            (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
                (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1} ∩
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) < ⊤ := by
  exact siegelSet_inter_slab_lt_top w₀ e he ι hι hw hfin hret hrec c C _hc a b _ha

open SiegelArchEmbed SiegelRealTransport in

private theorem w0b_of_record
    (c C : ℝ) (_hc : 0 < c) (a b : ℝ) (_ha : 0 < a) (_hab : a < b) :
    NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
        ({g : AdelicGL 3 (𝓞 ℚ) ℚ | ∃ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, g = n * t * k ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
          ∀ w : InfinitePlace ℚ,
            (∀ i j : Fin 3,
              (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
              (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
              ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
            (∀ i j : Fin 3, i ≠ j →
              (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
            (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
                (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1} ∩
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) < ⊤ := by
  have hreal := isReal_of_rat Rat.infinitePlace
  exact slab_lt_top_k1_shape Rat.infinitePlace (InfinitePlace.Completion.ringEquivRealOfIsReal hreal)
    (norm_symm_ringEquivRealOfIsReal hreal) (archEmbed3 ℚ Rat.infinitePlace)
    (continuous_archEmbed3 Rat.infinitePlace)
    (fun w => Subsingleton.elim w Rat.infinitePlace) (fun u p => componentAt3_archEmbed3 Rat.infinitePlace p u)
    (fun u => archPlaceComponent3_archEmbed3_self Rat.infinitePlace u)
    (fun g hg => archEmbed3_archPlaceComponent3_of_forall_componentAt3 Rat.infinitePlace hg) c C _hc a b _ha _hab

end SiegelAssembly

end

open Matrix IsDedekindDomain NumberField

theorem solution
    (c C : ℝ) (_hc : 0 < c) (a b : ℝ) (_ha : 0 < a) (_hab : a < b) :
    NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
        ({g : AdelicGL 3 (𝓞 ℚ) ℚ | ∃ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, g = n * t * k ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
          ∀ w : InfinitePlace ℚ,
            (∀ i j : Fin 3,
              (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
              (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
              ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
            (∀ i j : Fin 3, i ≠ j →
              (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
            (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
                (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1} ∩
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) < ⊤ := by
  exact SiegelAssembly.w0b_of_record c C _hc a b _ha _hab

end S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top (solution)
