-- Prove2me | solution 1 for N25.unitResidues25_bernoulli_zero_of_five_dvd
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:49.205775+00:00
-- url     : https://prove2.me/submissions/664b65ef-1126-42eb-936e-f5013cd08d11

import Mathlib
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false

namespace N25

/-- The adjacent Bernoulli difference vanishes on all five multiples of five. -/
theorem _root_.solution (a : ℤ) (ha : 5 ∣ a) (i : Fin 5) :
    let B : ℕ → ℚ := fun g =>
      (((a * (g : ℤ)) % 25 : ℤ) : ℚ) ^ 2 / 625 -
        (((a * (g : ℤ)) % 25 : ℤ) : ℚ) / 25 + 1 / 6
    B (unitResidues25 i).1 + B (unitResidues25 i).2 -
      (B (unitResidues25 (i + 1)).1 + B (unitResidues25 (i + 1)).2) = 0 := by
  have ht : ∀ (t : Fin 5) (j : Fin 5),
      let B : ℕ → ℚ := fun g =>
        (((5 * t.val * g) % 25 : ℕ) : ℚ) ^ 2 / 625 -
          (((5 * t.val * g) % 25 : ℕ) : ℚ) / 25 + 1 / 6
      B (unitResidues25 j).1 + B (unitResidues25 j).2 -
        (B (unitResidues25 (j + 1)).1 + B (unitResidues25 (j + 1)).2) = 0 := by
    intro t j
    fin_cases t <;> fin_cases j <;> decide +kernel
  obtain ⟨k, hk⟩ := ha
  let t : Fin 5 := ⟨(k % 5).toNat, by omega⟩
  have hrem : a % 25 = 5 * (t.val : ℤ) := by dsimp [t]; omega
  have hm (g : ℕ) : (((5 * t.val * g) % 25 : ℕ) : ℤ) = (a * (g : ℤ)) % 25 := by
    rw [Int.natCast_mod, Int.natCast_mul, Int.natCast_mul]
    norm_num only [Nat.cast_ofNat]
    rw [← hrem]
    simp only [Int.mul_emod, Int.emod_emod]
  have hq (g : ℕ) : (((5 * t.val * g) % 25 : ℕ) : ℚ) =
      (((a * (g : ℤ)) % 25 : ℤ) : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) (hm g)
  have h := ht t i
  dsimp only at h ⊢
  simpa only [hq] using h

end N25
