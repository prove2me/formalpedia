-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.matFourier22_comp_inv_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/23f5ebc6-727f-52ac-86f9-5e9e797f2fed

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Theorems.Thm_LanglandsTunnell_CubicInduction_colFourier23_comp_colwise_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_matFourier22_comp_inv_mul_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

namespace MF22COV

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (v.adicCompletion ℚ)
local notation "M22" => (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
local notation "M23" => (Matrix (Fin 2) (Fin 3) (v.adicCompletion ℚ))
local notation "G2" => (GL (Fin 2) (v.adicCompletion ℚ))

noncomputable def pad (X : M22) : M23 := Matrix.of fun i k => if h : (k : ℕ) < 2 then X i ⟨k, h⟩ else 0

noncomputable def cut (Y : M23) : M22 := Matrix.of fun i k => Y i (Fin.castSucc k)

theorem pad_castSucc (X : M22) (i : Fin 2) (k : Fin 2) : pad v X i (Fin.castSucc k) = X i k := by
  have hk : ((Fin.castSucc k : Fin 3) : ℕ) < 2 := by simp [k.isLt]
  simp only [pad, Matrix.of_apply, dif_pos hk]
  congr 1

theorem pad_two (X : M22) (i : Fin 2) : pad v X i 2 = 0 := by simp [pad]

theorem cut_setCol23_pad (X : M22) (j : Fin 2) (u : F × F) :
    cut v (setCol23 v (pad v X) (Fin.castSucc j) u) = setCol22 v X j u := by
  ext i k
  simp only [cut, Matrix.of_apply, setCol23_apply, setCol22_apply]
  by_cases hk : k = j
  · subst hk; simp
  · have : (Fin.castSucc k : Fin 3) ≠ Fin.castSucc j := fun h => hk (Fin.castSucc_injective _ h)
    rw [if_neg this, if_neg hk, pad_castSucc]

theorem colFourier22_eq_colFourier23_cut_pad (η : AddChar F ℂ) (ψ : M22 → ℂ) (j : Fin 2) (X : M22) :
    colFourier22 v η j ψ X = colFourier23 v η (Fin.castSucc j) (fun Y => ψ (cut v Y)) (pad v X) := by
  simp only [colFourier23_apply, colFourier22_apply, cut_setCol23_pad, pad_castSucc]

noncomputable def cw2 (B : Fin 2 → G2) (Y : M22) : M22 := Matrix.of fun i k => ∑ i' : Fin 2, ((B k : G2) : M22) i i' * Y i' k
noncomputable def cw3 (A : Fin 3 → G2) (Y : M23) : M23 := Matrix.of fun i k => ∑ i' : Fin 2, ((A k : G2) : M22) i i' * Y i' k

noncomputable def ext3 (B : Fin 2 → G2) : Fin 3 → G2 := fun k => if h : (k : ℕ) < 2 then B ⟨k, h⟩ else 1

theorem ext3_castSucc (B : Fin 2 → G2) (k : Fin 2) : ext3 v B (Fin.castSucc k) = B k := by
  have hk : ((Fin.castSucc k : Fin 3) : ℕ) < 2 := by simp [k.isLt]
  simp only [ext3, dif_pos hk]
  congr 1

theorem ext3_two (B : Fin 2 → G2) : ext3 v B 2 = 1 := by simp [ext3]

theorem cut_cw3_ext3 (B : Fin 2 → G2) (Y : M23) : cut v (cw3 v (ext3 v B) Y) = cw2 v B (cut v Y) := by
  ext i k; simp only [cut, cw3, cw2, Matrix.of_apply, ext3_castSucc]

theorem update_ext3 (B : Fin 2 → G2) (j : Fin 2) (g : G2) :
    Function.update (ext3 v B) (Fin.castSucc j) g = ext3 v (Function.update B j g) := by
  funext k
  by_cases hk : k = Fin.castSucc j
  · subst hk; rw [Function.update_self, ext3_castSucc, Function.update_self]
  · rw [Function.update_of_ne hk]
    by_cases hk2 : (k : ℕ) < 2
    · have : k = Fin.castSucc ⟨k, hk2⟩ := by ext; simp
      rw [this, ext3_castSucc, ext3_castSucc, Function.update_of_ne]
      intro h; apply hk; rw [this, h]
    · have : k = 2 := by ext; simp; omega
      subst this; rw [ext3_two, ext3_two]

theorem cw3_ext3_pad (B : Fin 2 → G2) (X : M22) : cw3 v (ext3 v B) (pad v X) = pad v (cw2 v B X) := by
  ext i k
  by_cases hk2 : (k : ℕ) < 2
  · have : k = Fin.castSucc ⟨k, hk2⟩ := by ext; simp
    rw [this]
    simp only [cw3, cw2, Matrix.of_apply, ext3_castSucc, pad_castSucc]
  · have : k = 2 := by ext; simp; omega
    subst this
    simp only [cw3, Matrix.of_apply, pad_two, mul_zero, Finset.sum_const_zero]

noncomputable def md (B : G2) : ℂ := ((modulus ((Matrix.GeneralLinearGroup.det B : Fˣ) : F) : ℝ) : ℂ)

theorem colFourier22_cw2 (η : AddChar F ℂ) (j : Fin 2) (B : Fin 2 → G2) (ψ : M22 → ℂ) (X : M22) :
    colFourier22 v η j (fun Y => ψ (cw2 v B Y)) X =
      (md v (B j))⁻¹ * colFourier22 v η j ψ (cw2 v (Function.update B j (transposeInvN (Fin 2) (B j))) X) := by
  rw [colFourier22_eq_colFourier23_cut_pad, colFourier22_eq_colFourier23_cut_pad]
  have hfun : (fun Y : M23 => ψ (cw2 v B (cut v Y))) = fun Y => (fun Z : M23 => ψ (cut v Z)) (cw3 v (ext3 v B) Y) := by
    funext Y; beta_reduce; rw [cut_cw3_ext3]
  rw [hfun]
  have h := LanglandsTunnell.CubicInduction.colFourier23_comp_colwise_eq v η (Fin.castSucc j) (ext3 v B)
    (fun Z : M23 => ψ (cut v Z)) (pad v X)
  rw [show (fun Y : M23 => (fun Z : M23 => ψ (cut v Z)) (Matrix.of fun i k => ∑ i' : Fin 2,
      ((ext3 v B k : G2) : M22) i i' * Y i' k)) = fun Y => (fun Z : M23 => ψ (cut v Z)) (cw3 v (ext3 v B) Y) from rfl] at h
  rw [h, ext3_castSucc, update_ext3, md]
  congr 2
  exact (cw3_ext3_pad v _ X)

theorem colFourier22_const_mul (η : AddChar F ℂ) (j : Fin 2) (c : ℂ) (Φ : M22 → ℂ) (X : M22) :
    colFourier22 v η j (fun Y => c * Φ Y) X = c * colFourier22 v η j Φ X := by
  rw [colFourier22_apply, colFourier22_apply, ← integral_const_mul]
  congr 1; funext u; ring

theorem md_inv (a : G2) : md v a⁻¹ = (md v a)⁻¹ := by
  simp only [md, map_inv]
  have hne : modulus ((Matrix.GeneralLinearGroup.det a : Fˣ) : F) ≠ 0 :=
    (modulus_pos (Matrix.GeneralLinearGroup.det a).ne_zero).ne'
  have hmul : modulus (((Matrix.GeneralLinearGroup.det a)⁻¹ : Fˣ) : F) * modulus ((Matrix.GeneralLinearGroup.det a : Fˣ) : F) = 1 := by
    rw [← modulus_mul, Units.inv_mul, modulus_one]
  have : modulus (((Matrix.GeneralLinearGroup.det a)⁻¹ : Fˣ) : F) = (modulus ((Matrix.GeneralLinearGroup.det a : Fˣ) : F))⁻¹ :=
    eq_inv_of_mul_eq_one_left hmul
  rw [this]; push_cast; ring

end MF22COV

open MF22COV in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (η : AddChar (v.adicCompletion ℚ) ℂ)
    (a : GL (Fin 2) (v.adicCompletion ℚ)) (φ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    matFourier22 v η (fun Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) =>
        φ (((a⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * Y)) X =
      ((modulus ((Matrix.GeneralLinearGroup.det a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ 2 *
        matFourier22 v η φ (Matrix.transpose ((a : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * X) := by
  classical

  set B : Fin 2 → GL (Fin 2) (v.adicCompletion ℚ) := fun _ => a⁻¹ with hB
  have hcw : ∀ Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      ((a⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * Y = MF22COV.cw2 v B Y := by
    intro Y; ext i k; simp only [MF22COV.cw2, Matrix.of_apply, Matrix.mul_apply, hB]
  have htr : transposeInvN (Fin 2) (a⁻¹) =
      ⟨Matrix.transpose ((a : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)),
       Matrix.transpose (((a⁻¹ : GL (Fin 2) (v.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)),
       by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one],
       by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]⟩ := by
    apply Units.ext; rw [coe_transposeInvN, inv_inv]
  set B1 : Fin 2 → GL (Fin 2) (v.adicCompletion ℚ) := Function.update B 1 (transposeInvN (Fin 2) (a⁻¹)) with hB1
  set B0 : Fin 2 → GL (Fin 2) (v.adicCompletion ℚ) := Function.update B1 0 (transposeInvN (Fin 2) (a⁻¹)) with hB0
  have hcw0 : ∀ Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      MF22COV.cw2 v B0 Y = Matrix.transpose ((a : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * Y := by
    have hk : ∀ k : Fin 2, B0 k = transposeInvN (Fin 2) (a⁻¹) := by
      rw [Fin.forall_fin_two]
      exact ⟨by simp [hB0], by simp [hB0, hB1]⟩
    intro Y; ext i k
    simp only [MF22COV.cw2, Matrix.of_apply, Matrix.mul_apply, hk, htr]
  simp_rw [hcw]
  rw [matFourier22_eq, matFourier22_eq]
  have h1 : colFourier22 v η 1 (fun Y => φ (MF22COV.cw2 v B Y)) =
      fun W => (MF22COV.md v (a⁻¹))⁻¹ * colFourier22 v η 1 φ (MF22COV.cw2 v B1 W) := by
    funext W; rw [MF22COV.colFourier22_cw2, hB1]
  rw [h1, MF22COV.colFourier22_const_mul, MF22COV.colFourier22_cw2]
  have hB10 : B1 0 = a⁻¹ := by rw [hB1, Function.update_of_ne (by decide)]
  rw [hB10, ← hB0, hcw0, MF22COV.md_inv, inv_inv, ← mul_assoc, ← pow_two]
  rfl

end S_LanglandsTunnell_CubicInduction_matFourier22_comp_inv_mul_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_matFourier22_comp_inv_mul_eq (solution)
