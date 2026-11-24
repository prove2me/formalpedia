-- Prove2me | solution 1 for GlobalTheory.BigCell.q_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:31.923913+00:00
-- url     : https://prove2.me/submissions/9e1514bb-3649-4efe-ab9c-929799674afa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BigCellFactorisationDoubledUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
open scoped Matrix
open Matrix
open GlobalTheory GlobalTheory.BigCell
variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
variable (f : R →+* R) (J : Matrix β β R) (K G : Matrix (β ⊕ β) (β ⊕ β) R) (Δ N : Matrix (β ⊕ β) β R)
  (Δt Nt : Matrix β (β ⊕ β) R) (D' : Matrix β β R)
namespace GlobalTheory.BigCell
theorem _root_.solution (h2 : Δ * Δt + N * Nt = (2 : R) • 1) (hD' : D' * (Nt * G * N) = 1) :
    (1 - ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt)) * G * N = N * (⅟(2 : R) • (Nt * G * N)) := by
  have hNN : N * Nt = (2 : R) • 1 - Δ * Δt := by rw [← h2]; abel
  have hD'r : D' * (Nt * (G * N)) = 1 := by rw [← hD']; simp only [Matrix.mul_assoc]
  calc (1 - ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt)) * G * N = G * N - ⅟(2 : R) • (Δ * (Δt * (G * N))) := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, hD'r, Matrix.mul_one]
    _ = N * (⅟(2 : R) • (Nt * G * N)) := by
        rw [Matrix.mul_smul, show N * (Nt * G * N) = N * Nt * G * N by simp only [Matrix.mul_assoc], hNN]
        simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_smul, invOf_mul_self, one_smul,
          Matrix.mul_assoc]
end GlobalTheory.BigCell
