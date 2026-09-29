-- Prove2me | solution 1 for Matrix.exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/93ba90ef-4b87-5dd3-a03d-a00343264c15

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul

set_option autoImplicit false

theorem solution
    (q : ℕ) (k : Type) [Field k] (φ : ZMod q →+* k)
    (B : Matrix (Fin 2) (Fin 2) k) (hB : B.det ≠ 0)
    (h : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) (ZMod q), ∃ c : k,
      B * (γ : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ = c • ((γ : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ * B)) :
    ∃ a : k, B = a • (1 : Matrix (Fin 2) (Fin 2) k) := by

  let u : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let v : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have hu : ((u : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ) = !![(1 : k), 1; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [u]
  have hv : ((v : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ) = !![(1 : k), 0; 1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [v]
  obtain ⟨c, hc⟩ := h u
  obtain ⟨c', hc'⟩ := h v
  rw [hu] at hc
  rw [hv] at hc'

  set a := B 0 0 with ha
  set b := B 0 1 with hb
  set p := B 1 0 with hp
  set d := B 1 1 with hd
  have hBe : B = !![a, b; p, d] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hdet : a * d - b * p ≠ 0 := by
    rw [hBe, Matrix.det_fin_two_of] at hB; exact hB
  rw [hBe] at hc hc'

  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  have f00 := congrFun (congrFun hc' 0) 0
  have f01 := congrFun (congrFun hc' 0) 1
  have f10 := congrFun (congrFun hc' 1) 0
  have f11 := congrFun (congrFun hc' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] at e00 e01 e10 e11 f00 f01 f10 f11

  have hp0 : p = 0 := by
    by_contra hp'
    have hc1 : c = 1 := by

      have : (c - 1) * p = 0 := by linear_combination (-1 : k) * e10
      rcases mul_eq_zero.mp this with h1 | h1
      · linear_combination h1
      · exact absurd h1 hp'
    subst hc1
    apply hp'
    linear_combination (-1 : k) * e00
  have had : a = d := by
    by_cases hc1 : c = 1
    · subst hc1; linear_combination e01
    ·
      exfalso
      have ha0 : a = 0 := by
        have : (c - 1) * a = 0 := by linear_combination (-1 : k) * e00 + (-c) * hp0
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd (by linear_combination h1) hc1
        · exact h1
      have hd0 : d = 0 := by
        have : (c - 1) * d = 0 := by linear_combination (-1 : k) * e11 + hp0
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd (by linear_combination h1) hc1
        · exact h1
      apply hdet
      rw [ha0, hd0, hp0]; ring

  have hb0 : b = 0 := by
    by_contra hb'
    have hc1 : c' = 1 := by
      have : (c' - 1) * b = 0 := by linear_combination (-1 : k) * f01
      rcases mul_eq_zero.mp this with h1 | h1
      · linear_combination h1
      · exact absurd h1 hb'
    subst hc1
    apply hb'
    linear_combination f00
  refine ⟨a, ?_⟩
  rw [hBe, hb0, hp0, ← had]
  ext i j; fin_cases i <;> fin_cases j <;> simp

end S_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul
end P2MW
export P2MW.S_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul (solution)
