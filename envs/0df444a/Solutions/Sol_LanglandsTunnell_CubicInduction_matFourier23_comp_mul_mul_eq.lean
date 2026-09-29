-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.matFourier23_comp_mul_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c6afa997-4f9a-5806-9476-6b12585ced98

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Theorems.Thm_LanglandsTunnell_CubicInduction_colFourier23_comp_colwise_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier23_comp_mul_transvection_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_matFourier23_comp_mul_mul_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

noncomputable section

open scoped Matrix

namespace MatTwist

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "M23" => (Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G2" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat2" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat3" => (Matrix (Fin 3) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

def md (B : G2) : ℂ := ((modulus ((Matrix.GeneralLinearGroup.det B : Fˣ) : F) : ℝ) : ℂ)

theorem md_def (B : G2) : md v B = ((modulus ((Matrix.GeneralLinearGroup.det B : Fˣ) : F) : ℝ) : ℂ) := rfl

theorem md_ne_zero (B : G2) : md v B ≠ 0 := by
  rw [md_def]
  exact_mod_cast (modulus_pos (Matrix.GeneralLinearGroup.det B).ne_zero).ne'

def cw (A : Fin 3 → G2) (Y : M23) : M23 := Matrix.of fun i k => ∑ i' : Fin 2, ((A k : G2) : Mat2) i i' * Y i' k

theorem cw_def (A : Fin 3 → G2) (Y : M23) :
    cw v A Y = Matrix.of fun i k => ∑ i' : Fin 2, ((A k : G2) : Mat2) i i' * Y i' k := rfl

theorem colFourier23_const_mul (η : AddChar F ℂ) (j : Fin 3) (c : ℂ) (Φ : M23 → ℂ) (X : M23) :
    colFourier23 v η j (fun Y => c * Φ Y) X = c * colFourier23 v η j Φ X := by
  rw [colFourier23_apply, colFourier23_apply, ← integral_const_mul]
  congr 1
  funext u
  ring

theorem col_cw (η : AddChar F ℂ) (j : Fin 3) (A : Fin 3 → G2) (ρ : M23 → ℂ) (X : M23) :
    colFourier23 v η j (fun Y => ρ (cw v A Y)) X =
      (md v (A j))⁻¹ * colFourier23 v η j ρ (cw v (Function.update A j (transposeInvN (Fin 2) (A j))) X) := by
  exact LanglandsTunnell.CubicInduction.colFourier23_comp_colwise_eq v η j A ρ X

theorem matFourier23_cw (η : AddChar F ℂ) (A : Fin 3 → G2) (ρ : M23 → ℂ) (X : M23) :
    matFourier23 v η (fun Y => ρ (cw v A Y)) X =
      (md v (A 0))⁻¹ * (md v (A 1))⁻¹ * (md v (A 2))⁻¹ *
        matFourier23 v η ρ (cw v (fun k => transposeInvN (Fin 2) (A k)) X) := by
  set A2 : Fin 3 → G2 := Function.update A 2 (transposeInvN (Fin 2) (A 2)) with hA2
  set A1 : Fin 3 → G2 := Function.update A2 1 (transposeInvN (Fin 2) (A2 1)) with hA1
  set A0 : Fin 3 → G2 := Function.update A1 0 (transposeInvN (Fin 2) (A1 0)) with hA0
  have hA21 : A2 1 = A 1 := by rw [hA2, Function.update_of_ne (by decide)]
  have hA10 : A1 0 = A 0 := by rw [hA1, Function.update_of_ne (by decide), hA2, Function.update_of_ne (by decide)]
  have hA0eq : A0 = fun k => transposeInvN (Fin 2) (A k) := by
    funext k
    fin_cases k <;> simp [hA0, hA1, hA2, Function.update_apply]
  rw [matFourier23_eq, matFourier23_eq]
  have h2 : colFourier23 v η 2 (fun Y => ρ (cw v A Y)) = fun W => (md v (A 2))⁻¹ * colFourier23 v η 2 ρ (cw v A2 W) := by
    funext W; rw [col_cw, hA2]
  rw [h2]
  have h1 : colFourier23 v η 1 (fun W => (md v (A 2))⁻¹ * colFourier23 v η 2 ρ (cw v A2 W)) =
      fun W => (md v (A 2))⁻¹ * ((md v (A 1))⁻¹ * colFourier23 v η 1 (colFourier23 v η 2 ρ)
        (cw v (Function.update A2 1 (transposeInvN (Fin 2) (A 1))) W)) := by
    funext W
    rw [colFourier23_const_mul, col_cw, hA21]
  rw [h1]
  have hA1' : Function.update A2 1 (transposeInvN (Fin 2) (A 1)) = A1 := by rw [hA1, hA21]
  rw [hA1']
  have h0 : colFourier23 v η 0 (fun W => (md v (A 2))⁻¹ * ((md v (A 1))⁻¹ *
      colFourier23 v η 1 (colFourier23 v η 2 ρ) (cw v A1 W))) X =
      (md v (A 2))⁻¹ * ((md v (A 1))⁻¹ * ((md v (A 0))⁻¹ *
        colFourier23 v η 0 (colFourier23 v η 1 (colFourier23 v η 2 ρ))
          (cw v (Function.update A1 0 (transposeInvN (Fin 2) (A 0))) X))) := by
    rw [colFourier23_const_mul]
    have : colFourier23 v η 0 (fun W => (md v (A 1))⁻¹ * colFourier23 v η 1 (colFourier23 v η 2 ρ) (cw v A1 W)) X =
        (md v (A 1))⁻¹ * ((md v (A 0))⁻¹ * colFourier23 v η 0 (colFourier23 v η 1 (colFourier23 v η 2 ρ))
          (cw v (Function.update A1 0 (transposeInvN (Fin 2) (A 0))) X)) := by
      rw [colFourier23_const_mul, col_cw, hA10]
    rw [this]
  have hA0' : Function.update A1 0 (transposeInvN (Fin 2) (A 0)) = A0 := by rw [hA0, hA10]
  rw [h0, hA0', hA0eq]
  ring

theorem cw_const (h : G2) (Y : M23) : cw v (fun _ => h) Y = ((h : G2) : Mat2) * Y := by
  ext i k
  rw [cw_def, Matrix.of_apply, Matrix.mul_apply]

theorem matFourier23_left (η : AddChar F ℂ) (h : G2) (ρ : M23 → ℂ) (X : M23) :
    matFourier23 v η (fun Y => ρ (((h : G2) : Mat2) * Y)) X =
      (md v h)⁻¹ ^ 3 * matFourier23 v η ρ (((transposeInvN (Fin 2) h : G2) : Mat2) * X) := by
  have := matFourier23_cw v η (fun _ => h) ρ X
  simp only [cw_const] at this
  rw [this]
  ring

end MatTwist

end

noncomputable section

open scoped Matrix

namespace MatTwist

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "M23" => (Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G2" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat2" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat3" => (Matrix (Fin 3) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

def mF (a : F) : ℂ := ((modulus a : ℝ) : ℂ)

theorem mF_def (a : F) : mF v a = ((modulus a : ℝ) : ℂ) := rfl

theorem mF_mul (a b : F) : mF v (a * b) = mF v a * mF v b := by
  simp only [mF_def, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]

theorem mF_one : mF v 1 = 1 := by simp [mF_def]

theorem mF_ne_zero {a : F} (ha : a ≠ 0) : mF v a ≠ 0 := by
  rw [mF_def]; exact_mod_cast (modulus_pos ha).ne'

theorem md_eq_mF (B : G2) : md v B = mF v ((B : G2) : Mat2).det := by
  rw [md_def, mF_def, Matrix.GeneralLinearGroup.val_det_apply]

theorem sb_comp_mul_right {N : Mat3} (hN : N.det ≠ 0) {ρ : M23 → ℂ} (hρ : IsSchwartzBruhat ρ) :
    IsSchwartzBruhat (fun Y : M23 => ρ (Y * N)) := by
  have hU : IsUnit N.det := isUnit_iff_ne_zero.2 hN
  let e : M23 ≃ₜ M23 :=
    { toFun := fun Y => Y * N
      invFun := fun Y => Y * N⁻¹
      left_inv := fun Y => by simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU]
      right_inv := fun Y => by simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  exact ⟨hρ.1.comp_continuous e.continuous, hρ.2.comp_homeomorph e⟩

theorem sb_comp_mul_left (h : G2) {ρ : M23 → ℂ} (hρ : IsSchwartzBruhat ρ) :
    IsSchwartzBruhat (fun Y : M23 => ρ (((h : G2) : Mat2) * Y)) := by
  let e : M23 ≃ₜ M23 :=
    { toFun := fun Y => ((h : G2) : Mat2) * Y
      invFun := fun Y => (((h⁻¹ : G2)) : Mat2) * Y
      left_inv := fun Y => by
        show (((h⁻¹ : G2)) : Mat2) * (((h : G2) : Mat2) * Y) = Y
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      right_inv := fun Y => by
        show ((h : G2) : Mat2) * ((((h⁻¹ : G2)) : Mat2) * Y) = Y
        rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      continuous_toFun := continuous_const.matrix_mul continuous_id
      continuous_invFun := continuous_const.matrix_mul continuous_id }
  exact ⟨hρ.1.comp_continuous e.continuous, hρ.2.comp_homeomorph e⟩

section Right

variable (η : AddChar (HeightOneSpectrum.adicCompletion ℚ v) ℂ)

def RT (N : Mat3) : Prop :=
  ∀ (ρ : M23 → ℂ), IsSchwartzBruhat ρ → ∀ X : M23,
    matFourier23 v η (fun Y => ρ (Y * N)) X = (mF v N.det)⁻¹ ^ 2 * matFourier23 v η ρ (X * (N⁻¹)ᵀ)

theorem RT_mul {A B : Mat3} (hA : A.det ≠ 0) (hB : B.det ≠ 0) (hPA : RT v η A) (hPB : RT v η B) :
    RT v η (A * B) := by
  intro ρ hρ X
  have hUA : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have hUB : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have hρB := sb_comp_mul_right v hB hρ
  have h1 : (fun Y : M23 => ρ (Y * (A * B))) = fun Y => (fun Z : M23 => ρ (Z * B)) (Y * A) := by
    funext Y; simp only [Matrix.mul_assoc]
  rw [h1, hPA _ hρB X, hPB _ hρ]
  have hinv : ((A * B)⁻¹)ᵀ = (A⁻¹)ᵀ * (B⁻¹)ᵀ := by
    rw [Matrix.mul_inv_rev, Matrix.transpose_mul]
  rw [hinv, Matrix.det_mul, mF_mul, ← Matrix.mul_assoc]
  have hA0 := mF_ne_zero v hA
  have hB0 := mF_ne_zero v hB
  field_simp

def scalarUnit (d : F) (hd : d ≠ 0) : G2 :=
  ⟨Matrix.scalar (Fin 2) d, Matrix.scalar (Fin 2) d⁻¹,
    by rw [← map_mul, mul_inv_cancel₀ hd, map_one],
    by rw [← map_mul, inv_mul_cancel₀ hd, map_one]⟩

theorem coe_scalarUnit (d : F) (hd : d ≠ 0) : ((scalarUnit v d hd : G2) : Mat2) = Matrix.scalar (Fin 2) d := rfl

theorem coe_inv_scalarUnit (d : F) (hd : d ≠ 0) :
    (((scalarUnit v d hd)⁻¹ : G2) : Mat2) = Matrix.scalar (Fin 2) d⁻¹ := rfl

theorem RT_diagonal (D : Fin 3 → F) (hD : (Matrix.diagonal D).det ≠ 0) : RT v η (Matrix.diagonal D) := by
  intro ρ hρ X
  have hDk : ∀ k, D k ≠ 0 := by
    intro k hk
    apply hD
    rw [Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ k) hk
  set A : Fin 3 → G2 := fun k => scalarUnit v (D k) (hDk k) with hA

  have hcw : (fun Y : M23 => ρ (Y * Matrix.diagonal D)) = fun Y => ρ (cw v A Y) := by
    funext Y
    congr 1
    ext i k
    rw [Matrix.mul_diagonal, cw_def, Matrix.of_apply, Fin.sum_univ_two]
    simp only [hA, coe_scalarUnit, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
      Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
    fin_cases i <;> simp <;> ring
  have hDinv : (Matrix.diagonal D)⁻¹ = Matrix.diagonal (fun k => (D k)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one using 2
    funext k; exact mul_inv_cancel₀ (hDk k)
  have hcw' : cw v (fun k => transposeInvN (Fin 2) (A k)) X = X * ((Matrix.diagonal D)⁻¹)ᵀ := by
    rw [hDinv, Matrix.diagonal_transpose]
    ext i k
    rw [Matrix.mul_diagonal, cw_def, Matrix.of_apply, Fin.sum_univ_two]
    simp only [coe_transposeInvN, hA, coe_inv_scalarUnit, Matrix.scalar_apply, Matrix.diagonal_transpose,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
      Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
    fin_cases i <;> simp <;> ring
  have hmd : ∀ k, md v (A k) = mF v (D k) * mF v (D k) := by
    intro k
    rw [md_eq_mF, hA, coe_scalarUnit, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two, mF_mul]
  rw [hcw, matFourier23_cw, hcw', hmd 0, hmd 1, hmd 2, Matrix.det_diagonal, Fin.prod_univ_three, mF_mul, mF_mul]
  have h0 := mF_ne_zero v (hDk 0)
  have h1 := mF_ne_zero v (hDk 1)
  have h2 := mF_ne_zero v (hDk 2)
  field_simp

theorem transpose_transvection (i j : Fin 3) (c : F) :
    (Matrix.transvection i j c)ᵀ = Matrix.transvection j i c := by
  rw [Matrix.transvection, Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]

theorem transvection_inv (i j : Fin 3) (hij : i ≠ j) (c : F) :
    (Matrix.transvection i j c)⁻¹ = Matrix.transvection i j (-c) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel, Matrix.transvection_zero]

theorem RT_transvection (n : ℤ)
    (hηn : ∀ x : HeightOneSpectrum.adicCompletion ℚ v, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : HeightOneSpectrum.adicCompletion ℚ v, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (t : Matrix.TransvectionStruct (Fin 3) F) : RT v η t.toMatrix := by
  intro ρ hρ X
  obtain ⟨i, j, hij, c⟩ := t
  rw [Matrix.TransvectionStruct.toMatrix_mk]
  rw [LanglandsTunnell.CubicInduction.matFourier23_comp_mul_transvection_eq v η n hηn hηn' ρ hρ i j hij c X,
    Matrix.det_transvection_of_ne i j hij, mF_one, inv_one, one_pow, one_mul, transvection_inv v i j hij,
    transpose_transvection]

theorem RT_of_det_ne_zero (n : ℤ)
    (hηn : ∀ x : HeightOneSpectrum.adicCompletion ℚ v, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : HeightOneSpectrum.adicCompletion ℚ v, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (N : Mat3) (hN : N.det ≠ 0) : RT v η N :=
  Matrix.diagonal_transvection_induction_of_det_ne_zero (RT v η) N hN
    (fun D hD => RT_diagonal v η D hD)
    (fun t => RT_transvection v η n hηn hηn' t)
    (fun A B hA hB hPA hPB => RT_mul v η hA hB hPA hPB)

end Right

end MatTwist

end

open scoped Matrix in
open MatTwist in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ)
    (hηn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → η x = 1)
    (hηn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ η x ≠ 1)
    (φ : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) → ℂ) (hφ : IsSchwartzBruhat φ)
    (h : GL (Fin 2) (v.adicCompletion ℚ)) (g : GL (Fin 3) (v.adicCompletion ℚ))
    (X : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ)) :
    matFourier23 v η (fun Y => φ ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * Y *
        (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) X =
      ((modulus ((Matrix.GeneralLinearGroup.det h : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ ^ 3 *
      ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹ ^ 2 *
        matFourier23 v η φ
          ((transposeInvN (Fin 2) h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * X *
            (transposeInvN (Fin 3) g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
  have hg : ((g : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det g).ne_zero
  have hψ := sb_comp_mul_left v h hφ
  have h1 : (fun Y : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) =>
      φ ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * Y * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) =
      fun Y => (fun Z : Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ) =>
        φ ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * Z)) (Y * (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
    funext Y; simp only [Matrix.mul_assoc]
  rw [h1, RT_of_det_ne_zero v η n hηn hηn' _ hg _ hψ X, matFourier23_left]
  have hgi : ((transposeInvN (Fin 3) g : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      (((g : GL (Fin 3) (v.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))⁻¹)ᵀ := by
    rw [coe_transposeInvN, Matrix.coe_units_inv]
  rw [hgi, md_def, mF_def, ← Matrix.GeneralLinearGroup.val_det_apply, Matrix.mul_assoc]
  ring

end S_LanglandsTunnell_CubicInduction_matFourier23_comp_mul_mul_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_matFourier23_comp_mul_mul_eq (solution)
