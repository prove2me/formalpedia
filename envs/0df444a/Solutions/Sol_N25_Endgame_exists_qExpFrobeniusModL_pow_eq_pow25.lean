-- Prove2me | solution 1 for N25.Endgame.exists_qExpFrobeniusModL_pow_eq_pow25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:48.884707+00:00
-- url     : https://prove2.me/submissions/c8938466-2297-4153-9896-54682963f634

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence

/-! Iterates of the prime q-expansion Frobenius on functions and places. -/
noncomputable section

namespace N25.Endgame

/-- Every prime-Frobenius iterate has enough power preimages to be integral. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    (n : ℕ) (x : ModularCurve.qExpFunctionFieldC K Γ25) :
    ∃ y : ModularCurve.qExpFunctionFieldC K Γ25,
      (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n) y = x ^ (p ^ n) := by
  induction n generalizing x with
  | zero => exact ⟨x, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ModularCurve.exists_qExpFrobeniusModL_eq_pow K Γ25 p x
    obtain ⟨y, hy⟩ := ih z
    refine ⟨y, ?_⟩
    rw [pow_succ', AlgHom.mul_apply, hy, map_pow, hz, ← pow_mul, pow_succ']

end N25.Endgame
