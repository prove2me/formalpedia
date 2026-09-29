-- Prove2me | solution 1 for Leopoldt.galois_totallyReal_injection_of_three_le_finrank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T20:23:25.690026+00:00
-- url     : https://prove2.me/submissions/4229bf50-7587-4b6c-b7e1-b58b5233aa7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Leopoldt_galois_totallyReal_injection_of_not_exponent_two
import Theorems.Thm_Leopoldt_leopoldt_totallyReal_multiquadratic
import Theorems.Thm_Leopoldt_leopoldtConjecture_iff_exists_continuous_injection

open NumberField

theorem solution (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (L : Type*) [Field L] [NumberField L] [IsTotallyReal L] [IsGalois ℚ L]
    (hL : 3 ≤ Module.finrank ℚ L) :
    ∃ f : Multiplicative (Fin (Units.rank L) → ℤ_[p]) →* Leopoldt.SemilocalUnits p L,
      Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ Leopoldt.unitClosure p L := by
  by_cases hG : ∃ σ : L ≃ₐ[ℚ] L, σ * σ ≠ 1
  · exact Leopoldt.galois_totallyReal_injection_of_not_exponent_two p hp L hL hG
  · push Not at hG
    exact (Leopoldt.leopoldtConjecture_iff_exists_continuous_injection p L).1
      (Leopoldt.leopoldt_totallyReal_multiquadratic p L hG)
