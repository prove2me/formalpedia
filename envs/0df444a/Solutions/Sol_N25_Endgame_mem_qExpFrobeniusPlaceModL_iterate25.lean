-- Prove2me | solution 1 for N25.Endgame.mem_qExpFrobeniusPlaceModL_iterate25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:50.074804+00:00
-- url     : https://prove2.me/submissions/f5366d1f-760a-49e2-ad99-e2e35fddbb69

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence

/-! Iterates of the prime q-expansion Frobenius on functions and places. -/
noncomputable section

namespace N25.Endgame

/-- Iterated place restriction is characterized by preimages under the iterated function map. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    (n : ℕ) (P : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K Γ25))
    (x : ModularCurve.qExpFunctionFieldC K Γ25) :
    x ∈ ((ModularCurve.qExpFrobeniusPlaceModL K Γ25 p)^[n] P).toValuationSubring ↔
      (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n) x ∈ P.toValuationSubring := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ModularCurve.mem_qExpFrobeniusPlaceModL_iff, ih]
    simp only [pow_succ, AlgHom.mul_apply]

end N25.Endgame
