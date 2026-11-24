-- Prove2me | solution 1 for GlobalTheory.HCXi.exists_unitary_comm_mul_eq_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:06:28.614639+00:00
-- url     : https://prove2.me/submissions/94be73fb-f7e5-43a9-9582-7375d33e09c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsUnitaryOfGramEq
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsUnitaryCommMulEqOfGram
import Theorems.Thm_GlobalTheory_UnitaryExtension_exists_unitary_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
namespace GlobalTheory.HCXi
open Matrix MeasureTheory in
open scoped ENNReal ComplexOrder in
private lemma exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero {n m : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Qᴴ = Q)
    (X Y : Matrix (Fin n) (Fin m) ℂ) (h : Xᴴ * X = Yᴴ * Y) (hX : Q * X = 0) (hY : Q * Y = 0) :
    ∃ W : Matrix (Fin n) (Fin n) ℂ, Wᴴ * W = 1 ∧ W * Q = Q ∧ W * X = Y := by
  have hXQ : Xᴴ * Q = 0 := by rw [← hQ, ← conjTranspose_mul, hX, conjTranspose_zero]
  have hYQ : Yᴴ * Q = 0 := by rw [← hQ, ← conjTranspose_mul, hY, conjTranspose_zero]
  have e2 : Xᴴ * Q = Yᴴ * Q := by rw [hXQ, hYQ]
  have e3 : Qᴴ * X = Qᴴ * Y := by rw [hQ, hX, hY]
  have hG : (fromCols X Q)ᴴ * fromCols X Q = (fromCols Y Q)ᴴ * fromCols Y Q := by
    ext (i | i) (j | j)
    · simpa [Matrix.mul_apply] using congrFun (congrFun h i) j
    · simpa [Matrix.mul_apply] using congrFun (congrFun e2 i) j
    · simpa [Matrix.mul_apply] using congrFun (congrFun e3 i) j
    · simp [Matrix.mul_apply]
  obtain ⟨W, hWu, hW⟩ := _root_.GlobalTheory.UnitaryExtension.exists_unitary_mul_eq _ _ hG
  rw [mul_fromCols, fromCols_inj.eq_iff] at hW
  exact ⟨W, hWu, hW.2, hW.1⟩
end GlobalTheory.HCXi
end

set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi
open Matrix MeasureTheory
open scoped ENNReal ComplexOrder
namespace GlobalTheory.HCXi
namespace _root_.GlobalTheory.HCXi
theorem _root_.solution {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : Hᴴ = H) (hHH : H * H = 1)
    (A B : Matrix (Fin n) (Fin m) ℂ) (h1 : Aᴴ * A = Bᴴ * B) (h2 : Aᴴ * H * A = Bᴴ * H * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * H = H * U ∧ U * A = B := by
  obtain ⟨Pp, hPp⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = (1 / 2 : ℂ) • (1 + H) := ⟨_, rfl⟩
  obtain ⟨Pm, hPm⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = (1 / 2 : ℂ) • (1 - H) := ⟨_, rfl⟩
  have hPpH : Ppᴴ = Pp := by simp [hPp, hH, conjTranspose_smul]
  have hPmH : Pmᴴ = Pm := by simp [hPm, hH, conjTranspose_smul]
  have hPpPp : Pp * Pp = Pp := by
    simp only [hPp, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hPmPm : Pm * Pm = Pm := by
    simp only [hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hPpPm : Pp * Pm = 0 := by
    simp only [hPp, hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hPmPp : Pm * Pp = 0 := by
    simp only [hPp, hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hsum : Pp + Pm = 1 := by rw [hPp, hPm]; module
  have hHdec : H = Pp - Pm := by rw [hPp, hPm]; module
  have h2' : Aᴴ * (H * A) = Bᴴ * (H * B) := by simpa only [Matrix.mul_assoc] using h2
  have gramP : ∀ Z : Matrix (Fin n) (Fin m) ℂ,
      (Pp * Z)ᴴ * (Pp * Z) = (1 / 2 : ℂ) • (Zᴴ * Z + Zᴴ * (H * Z)) := by
    intro Z
    rw [conjTranspose_mul, hPpH, Matrix.mul_assoc, ← Matrix.mul_assoc Pp, hPpPp, hPp]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul]
  have gramM : ∀ Z : Matrix (Fin n) (Fin m) ℂ,
      (Pm * Z)ᴴ * (Pm * Z) = (1 / 2 : ℂ) • (Zᴴ * Z - Zᴴ * (H * Z)) := by
    intro Z
    rw [conjTranspose_mul, hPmH, Matrix.mul_assoc, ← Matrix.mul_assoc Pm, hPmPm, hPm]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]
  obtain ⟨Wp, hWpu, hWpP, hWpA⟩ := exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero Pm hPmH (Pp * A) (Pp * B)
    (by rw [gramP, gramP, h1, h2']) (by rw [← Matrix.mul_assoc, hPmPp, Matrix.zero_mul])
    (by rw [← Matrix.mul_assoc, hPmPp, Matrix.zero_mul])
  obtain ⟨Wm, hWmu, hWmP, hWmA⟩ := exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero Pp hPpH (Pm * A) (Pm * B)
    (by rw [gramM, gramM, h1, h2']) (by rw [← Matrix.mul_assoc, hPpPm, Matrix.zero_mul])
    (by rw [← Matrix.mul_assoc, hPpPm, Matrix.zero_mul])
  have hWpHPm : Wpᴴ * Pm = Pm := by rw [← hWpP, ← Matrix.mul_assoc, hWpu, Matrix.one_mul, hWpP]
  have hWmHPp : Wmᴴ * Pp = Pp := by rw [← hWmP, ← Matrix.mul_assoc, hWmu, Matrix.one_mul, hWmP]
  have hPmWp : Pm * Wp = Pm := by
    have := congrArg conjTranspose hWpHPm
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, hPmH] at this
  have hPpWm : Pp * Wm = Pp := by
    have := congrArg conjTranspose hWmHPp
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, hPpH] at this
  have hA : Pp * Wp * Pp = Wp * Pp := calc
    Pp * Wp * Pp = (Pp + Pm) * Wp * Pp - Pm * Wp * Pp := by
      rw [Matrix.add_mul, Matrix.add_mul]; abel
    _ = Wp * Pp := by rw [hsum, Matrix.one_mul, hPmWp, hPmPp, sub_zero]
  have hB : Pm * Wm * Pm = Wm * Pm := calc
    Pm * Wm * Pm = (Pp + Pm) * Wm * Pm - Pp * Wm * Pm := by
      rw [Matrix.add_mul, Matrix.add_mul]; abel
    _ = Wm * Pm := by rw [hsum, Matrix.one_mul, hPpWm, hPpPm, sub_zero]
  have hX1 : Pp * Wpᴴ * Wp = Pp := by rw [Matrix.mul_assoc, hWpu, Matrix.mul_one]
  have hX2 : Pm * Wmᴴ * Wm = Pm := by rw [Matrix.mul_assoc, hWmu, Matrix.mul_one]
  have hX3 : Pp * Wpᴴ * Wm * Pm = 0 := calc
    Pp * Wpᴴ * Wm * Pm = Pp * Wpᴴ * (Pm * Wm * Pm) := by rw [hB, Matrix.mul_assoc (Pp * Wpᴴ)]
    _ = Pp * (Wpᴴ * Pm) * Wm * Pm := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hWpHPm, hPpPm, Matrix.zero_mul, Matrix.zero_mul]
  have hX4 : Pm * Wmᴴ * Wp * Pp = 0 := calc
    Pm * Wmᴴ * Wp * Pp = Pm * Wmᴴ * (Pp * Wp * Pp) := by rw [hA, Matrix.mul_assoc (Pm * Wmᴴ)]
    _ = Pm * (Wmᴴ * Pp) * Wp * Pp := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hWmHPp, hPmPp, Matrix.zero_mul, Matrix.zero_mul]
  refine ⟨Wp * Pp + Wm * Pm, ?_, ?_, ?_⟩
  · simp only [conjTranspose_add, conjTranspose_mul, hPpH, hPmH, Matrix.add_mul, Matrix.mul_add,
      ← Matrix.mul_assoc, hX1, hX2, hX3, hX4, hPpPp, hPmPm]
    rw [add_zero, zero_add, hsum]
  · have hUH : (Wp * Pp + Wm * Pm) * H = Wp * Pp - Wm * Pm := by
      rw [hHdec]
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc, hPpPp, hPpPm, hPmPp, hPmPm,
        Matrix.mul_zero]
      abel
    have hHU : H * (Wp * Pp + Wm * Pm) = Wp * Pp - Wm * Pm := by
      rw [hHdec]
      simp only [Matrix.sub_mul, Matrix.mul_add, ← Matrix.mul_assoc, hPpWm, hPmWp, hPpPm, hPmPp,
        hA, hB]
      abel
    rw [hUH, hHU]
  · rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hWpA, hWmA, ← Matrix.add_mul, hsum,
      Matrix.one_mul]
end _root_.GlobalTheory.HCXi
end GlobalTheory.HCXi
