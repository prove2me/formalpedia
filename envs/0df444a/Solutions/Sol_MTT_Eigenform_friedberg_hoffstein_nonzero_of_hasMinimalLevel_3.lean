-- Prove2me | solution 3 for MTT.Eigenform.friedberg_hoffstein_nonzero_of_hasMinimalLevel
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-26T20:52:00.502263+00:00
-- url     : https://prove2.me/submissions/f3867ff9-1715-4443-8fd9-391547904809
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MTT_Eigenform_epsilon_neg_one_eq_neg_one_pow
import Theorems.Thm_HorizontalPadicL_exists_prime_quadraticCharacter_prescribed_sign
import Theorems.Thm_MTT_Eigenform_exists_frickeRootNumber_quadratic_twist
import Theorems.Thm_MTT_Eigenform_friedberg_hoffstein_infinite_of_admissible_seed

set_option autoImplicit false

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
    exists_quadratic_seed_of_sign hN f.epsilon
      (by simpa only [heven.neg_one_pow] using f.epsilon_neg_one_eq_neg_one_pow) d hd s
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
