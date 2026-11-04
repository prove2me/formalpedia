-- Prove2me | solution 1 for Light.polyBound_pair_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:51.895016+00:00
-- url     : https://prove2.me/submissions/5025d9d8-5b38-4a6b-9cd7-7a932a2b7a1c

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize

set_option autoImplicit false
section
open Light
open ThreeSumApsp.WordRam
namespace Light
theorem _root_.solution {s k p₁ p₂ n : ℕ} (h₁ : p₁ ≤ n) (h₂ : p₂ ≤ n) :
    polyBound s k [p₁, p₂] ≤ polyBound s (2 * k) [n] := by
  have hprod : (p₁ + 1) * (p₂ + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hpair : polyBound s k [p₁, p₂] = 2 ^ s * ((p₁ + 1) * (p₂ + 1)) ^ k := by simp [polyBound]
  have hone : polyBound s (2 * k) [n] = 2 ^ s * ((n + 1) * (n + 1)) ^ k := by
    simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← pow_two, ← pow_mul]
  rw [hpair, hone]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hprod k)
end Light
