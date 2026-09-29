-- Prove2me | solution 2 for MTT.Eigenform.friedberg_hoffstein_nonzero_of_hasMinimalLevel
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-26T20:19:37.220567+00:00
-- url     : https://prove2.me/submissions/4b7e6b84-6525-451e-8b77-59f9f2248207
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MTT_Arithmetic
import Theorems.Thm_HorizontalPadicL_exists_prime_quadraticCharacter_prescribed_sign
import Theorems.Thm_MTT_Eigenform_exists_frickeRootNumber_quadratic_twist
import Theorems.Thm_MTT_Eigenform_friedberg_hoffstein_infinite_of_admissible_seed

set_option autoImplicit false

namespace MTT.Eigenform

/-- A normalized eigenform is nonzero as a function. -/
theorem exists_form_ne_zero {N k : ℕ} {ι : Qbar →+* ℂ} (f : Eigenform N k ι) :
    ∃ z : UpperHalfPlane, f.form z ≠ 0 := by
  by_contra! h
  have hf : (f.form : UpperHalfPlane → ℂ) = 0 := funext h
  have hcoeff := f.coeff_eq 1
  simp [hf, UpperHalfPlane.qExpansion_zero, f.normalized] at hcoeff

/-- The nebentype of a normalized eigenform of even weight is even. -/
theorem epsilon_neg_one_eq_one {N k : ℕ} {ι : Qbar →+* ℂ}
    (f : Eigenform N k ι) (heven : Even k) : f.epsilon (-1) = 1 := by
  obtain ⟨z, hz⟩ := f.exists_form_ne_zero
  let γ : CongruenceSubgroup.Gamma0 N := ⟨-1, by simp⟩
  have h := f.character_law γ z
  have hact : Matrix.SpecialLinearGroup.mapGL ℝ γ.val • z = z := by
    change (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z = z
    simp
  rw [hact] at h
  have h' : f.form z = ι (f.epsilon (-1)) * f.form z := by
    simpa [γ, heven.neg_one_pow] using h
  apply ι.injective
  rw [map_one]
  exact (mul_right_cancel₀ hz (by simpa using h'.symm) : ι (f.epsilon (-1)) = 1)

end MTT.Eigenform

namespace HorizontalPadicL

/-- Apply the prime-conductor arithmetic theorem to construct the seed used in
the minimal-level Friedberg--Hoffstein reduction. -/
theorem exists_quadratic_seed_of_sign {N : ℕ} (hN : 0 < N)
    (ε : DirichletCharacter MTT.Qbar N) (hε : ε (-1) = 1)
    (d : ℕ) (hd : 0 < d) (s : Bool) :
    ∃ η : DirichletCharacterWithLevel,
      η.2.IsPrimitive ∧ orderOf η.2 = 2 ∧ Nat.Coprime (N * d) η.1.1 ∧
      ε η.1.1 = 1 ∧ η.2 (-N) = (if s then 1 else -1) := by
  obtain ⟨η, _, _, hcong, hprim, horder, hcop, hpar, hdiv⟩ :=
    exists_prime_quadraticCharacter_prescribed_sign (N * d) (Nat.mul_pos hN hd) s 2
  have hqN : (η.1.1 : ZMod N) = if s then 1 else -1 := by
    have h := congrArg
      (ZMod.castHom (dvd_mul_of_dvd_right (dvd_mul_right N d) 8) (ZMod N)) hcong
    simpa only [map_natCast, apply_ite, map_one, map_neg] using h
  have hεq : ε η.1.1 = 1 := by
    rw [hqN]
    cases s <;> simp [hε]
  change η.2.conductor = η.1.1 at hprim
  refine ⟨η, hprim, horder, ?_, hεq, ?_⟩
  · simpa only [hprim] using hcop
  · rw [neg_eq_neg_one_mul, map_mul, hdiv N hN (dvd_mul_right N d), mul_one]
    exact hpar

end HorizontalPadicL

open HorizontalPadicL

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hmin : f.HasMinimalLevel) (d : ℕ) (hd : 0 < d) :
    ∃ η : DirichletCharacterWithLevel,
      η.2.IsPrimitive ∧
      orderOf η.2 = 2 ∧
      Nat.Coprime (N * d) η.2.conductor ∧
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0 := by
  classical
  obtain ⟨w, _, _, hsign, htwist⟩ :=
    f.exists_frickeRootNumber_quadratic_twist hN hk heven ι hmin
  obtain ⟨s, hs⟩ : ∃ s : Bool,
      f.HasRealCoefficients → w * (if s then (1 : ℂ) else -1) = 1 := by
    by_cases hreal : f.HasRealCoefficients
    · rcases hsign hreal with hw | hw
      · exact ⟨true, fun _ ↦ by simp [hw]⟩
      · exact ⟨false, fun _ ↦ by simp [hw]⟩
    · exact ⟨true, fun h ↦ (hreal h).elim⟩
  obtain ⟨η₀, hprimitive, horder, hcop, hε, hηN⟩ :=
    exists_quadratic_seed_of_sign hN f.epsilon (f.epsilon_neg_one_eq_one heven) d hd s
  have hadmissible : f.HasRealCoefficients →
      MTT.HasFrickeRootNumber
        (@MTT.inverseTwist ι f.form η₀.1.1 ⟨Nat.ne_of_gt η₀.1.2⟩ η₀.2)
        (N * η₀.1.1 ^ 2) k 1 := by
    intro hreal
    have hroot := htwist η₀ hprimitive horder (Nat.coprime_mul_iff_left.mp hcop).1
    have hscalar : w * ι (f.epsilon η₀.1.1) * ι (η₀.2 (-N)) = 1 := by
      rw [hε, map_one, mul_one, hηN]
      simpa only [apply_ite, map_one, map_neg] using hs hreal
    simpa only [hscalar] using hroot
  obtain ⟨η, hη⟩ :=
    (f.friedberg_hoffstein_infinite_of_admissible_seed hN hk heven ι hmin d hd
      η₀ hprimitive horder hcop hadmissible).nonempty
  exact ⟨η, hη.1, hη.2.1, hη.2.2.1, hη.2.2.2.2.2⟩
