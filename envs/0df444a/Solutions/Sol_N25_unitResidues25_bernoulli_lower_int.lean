-- Prove2me | solution 1 for N25.unitResidues25_bernoulli_lower_int
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:12.027114+00:00
-- url     : https://prove2.me/submissions/a2f90380-f212-4baf-a180-f90accf70625

import Mathlib
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_unitResidues25_bernoulli_lower

set_option autoImplicit false

namespace N25

theorem _root_.solution (a : ℤ) (i : Fin 5) :
    let B : ℕ → ℚ := fun g =>
      (((a * (g : ℤ)) % 25 : ℤ) : ℚ) ^ 2 / 625 -
        (((a * (g : ℤ)) % 25 : ℤ) : ℚ) / 25 + 1 / 6
    (-6 / 25 : ℚ) ≤ B (unitResidues25 i).1 + B (unitResidues25 i).2 -
      (B (unitResidues25 (i + 1)).1 + B (unitResidues25 (i + 1)).2) := by
  let t : Fin 25 := ⟨(a % 25).toNat, by omega⟩
  have ht : (t.val : ℤ) = a % 25 := by dsimp [t]; omega
  have hm (g : ℕ) : (((t.val * g) % 25 : ℕ) : ℤ) = (a * (g : ℤ)) % 25 := by
    rw [Int.natCast_mod, Int.natCast_mul, ht]
    norm_num only [Nat.cast_ofNat]
    simp only [Int.mul_emod, Int.emod_emod]
  have hq (g : ℕ) : (((t.val * g) % 25 : ℕ) : ℚ) = (((a * (g : ℤ)) % 25 : ℤ) : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun x : ℤ => (x : ℚ)) (hm g)
  have h := unitResidues25_bernoulli_lower t i
  dsimp only at h ⊢
  simpa only [hq] using h

end N25
