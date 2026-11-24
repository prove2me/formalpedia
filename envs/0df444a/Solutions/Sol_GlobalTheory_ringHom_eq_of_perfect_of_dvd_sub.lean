-- Prove2me | solution 1 for GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:42.814233+00:00
-- url     : https://prove2.me/submissions/6346df9d-81cd-42a7-a4b3-789b177f38de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RingHomEqOfPerfectOfDvdSubAdicSeparated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by
  intro l _ R O _ _ _ _ _ x e he hH ψ ψ' h
  ext y
  rw [← sub_eq_zero]
  apply hH.haus
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  obtain ⟨z, rfl⟩ : ∃ z : R, z ^ l ^ n = y :=
    ⟨(iterateFrobeniusEquiv R l n).symm y, by
      have hs := (iterateFrobeniusEquiv R l n).apply_symm_apply y
      rwa [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at hs⟩
  rw [map_pow, map_pow, ← sub_pow_char_pow]
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hn : n ≤ e * l ^ n :=
    (Nat.lt_pow_self (by omega)).le.trans (Nat.le_mul_of_pos_left _ he)
  exact (pow_dvd_pow x hn).trans (by rw [pow_mul]; exact pow_dvd_pow_of_dvd (h z) _)
end GlobalTheory
