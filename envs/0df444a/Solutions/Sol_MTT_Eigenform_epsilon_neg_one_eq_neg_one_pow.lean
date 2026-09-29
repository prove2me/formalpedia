-- Prove2me | solution 1 for MTT.Eigenform.epsilon_neg_one_eq_neg_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-26T20:51:10.62126+00:00
-- url     : https://prove2.me/submissions/4a8c0ded-6330-4eae-88ac-7a90fd9dc478

import Definitions.Def_MTT_Arithmetic

set_option autoImplicit false

private theorem exists_form_ne_zero {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (f : MTT.Eigenform N k ι) : ∃ z : UpperHalfPlane, f.form z ≠ 0 := by
  by_contra! h
  have hf : (f.form : UpperHalfPlane → ℂ) = 0 := funext h
  have hcoeff := f.coeff_eq 1
  simp [hf, UpperHalfPlane.qExpansion_zero, f.normalized] at hcoeff

/-- The nebentype of a normalized eigenform has the same parity as its weight. -/
theorem solution {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (f : MTT.Eigenform N k ι) : f.epsilon (-1) = (-1) ^ k := by
  obtain ⟨z, hz⟩ := exists_form_ne_zero f
  let γ : CongruenceSubgroup.Gamma0 N := ⟨-1, by simp⟩
  have h := f.character_law γ z
  have hact : Matrix.SpecialLinearGroup.mapGL ℝ γ.val • z = z := by
    change (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z = z
    simp
  rw [hact] at h
  have h' : f.form z = ι (f.epsilon (-1)) * (-1 : ℂ) ^ k * f.form z := by
    simpa [γ] using h
  have hprod : ι (f.epsilon (-1)) * (-1 : ℂ) ^ k = 1 :=
    mul_right_cancel₀ hz (by simpa using h'.symm)
  apply ι.injective
  simp only [map_pow, map_neg, map_one]
  apply mul_right_cancel₀ (pow_ne_zero k (neg_ne_zero.mpr one_ne_zero))
  simpa only [← mul_pow, neg_mul_neg, one_mul, one_pow] using hprod
