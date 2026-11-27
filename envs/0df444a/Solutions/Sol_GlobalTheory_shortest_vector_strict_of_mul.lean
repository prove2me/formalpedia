-- Prove2me | solution 1 for GlobalTheory.shortest_vector_strict_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:41:15.221805+00:00
-- url     : https://prove2.me/submissions/38c4b2a1-a3e0-4284-a048-6bb0cde795d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ShortestVectorStrictOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (B : X →+ X →+ ℤ), (∀ a b, Q (a + b) = Q a + Q b + B a b) → (∀ a, 2 * Q a = B a a) → (∀ a, a ≠ 0 → 1 ≤ Q a) → ∀ (n r : ℕ), 1 ≤ n → 2 ≤ r → ∀ z : X, (∀ m, Q z ≤ Q (z + n • m)) → ∀ m : X, (n * r) • m ≠ 0 → Q z < Q (z + (n * r) • m) := by
  intro X _ Q B hadd hdiag hpos n r _ hr z hmin m hm
  have hnr : (n * r) • m = r • (n • m) := by rw [mul_comm, mul_smul]
  rw [hnr] at hm ⊢
  have h1 := hmin m
  generalize n • m = a at hm h1
  have ha : a ≠ 0 := by
    rintro rfl
    exact hm (smul_zero _)
  have hQa := hpos a ha
  have h2 : 2 * Q (r • a) = (r : ℤ) * ((r : ℤ) * (2 * Q a)) := by
    rw [hdiag, hdiag]
    simp only [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul]
  have h3 : B z (r • a) = (r : ℤ) * B z a := by
    simp only [map_nsmul, nsmul_eq_mul]
  rw [hadd] at h1 ⊢
  rw [h3]
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have h4 : 0 ≤ (r : ℤ) * (Q a + B z a) := mul_nonneg (by omega) (by omega)
  have h5 : 0 < ((r : ℤ) * (r - 1)) * Q a :=
    mul_pos (mul_pos (by omega) (by omega)) (by omega)
  nlinarith
end GlobalTheory
