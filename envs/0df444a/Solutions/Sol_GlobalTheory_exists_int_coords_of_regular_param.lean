-- Prove2me | solution 1 for GlobalTheory.exists_int_coords_of_regular_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:34:15.478386+00:00
-- url     : https://prove2.me/submissions/6aadbcae-d3c7-44a4-90be-34ff9225e2f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsIntCoordsOfRegularParam

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
theorem _root_.solution (n : ℕ) (u : ℕ → ℝ)
    (h : ∀ i ∈ Finset.Icc 1 n, ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) :
    ∃ (β : ℂ) (L : Fin (n + 1) → ℤ), StrictAnti L ∧
      (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) ∧
      ∀ i j : Fin (n + 1), (L i : ℝ) - (L j : ℝ) = u ((i : ℕ) + 1) - u ((j : ℕ) + 1) := by
  have key : ∀ j : ℕ, j ≤ n → ∃ z : ℤ, (z : ℝ) = u (j + 1) - u 1 := by
    intro j
    induction j with
    | zero => intro _; exact ⟨0, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨z, hz⟩ := ih (by omega)
      obtain ⟨N, hN⟩ := h (k + 1) (Finset.mem_Icc.2 ⟨by omega, hk⟩)
      refine ⟨z - N - 1, ?_⟩
      push_cast
      linarith
  choose z hz using key
  refine ⟨(u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2, fun j => z j (Nat.lt_succ_iff.1 j.2), ?_, ?_, ?_⟩
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    obtain ⟨N, hN⟩ := h (i + 1) (Finset.mem_Icc.2 ⟨by omega, i.2⟩)
    have h1 := hz (i.succ : Fin (n + 1)) (Nat.lt_succ_iff.1 i.succ.2)
    have h2 := hz (i.castSucc : Fin (n + 1)) (Nat.lt_succ_iff.1 i.castSucc.2)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : ((z (i.succ : Fin (n + 1)) (Nat.lt_succ_iff.1 i.succ.2) : ℤ) : ℝ)
        < (z (i.castSucc : Fin (n + 1)) (Nat.lt_succ_iff.1 i.castSucc.2) : ℤ) := by
      rw [h1, h2]
      simp only [Fin.val_succ, Fin.val_castSucc]
      linarith
    exact_mod_cast this
  · intro j
    have h1 := congrArg (fun x : ℝ => (x : ℂ)) (hz j (Nat.lt_succ_iff.1 j.2))
    simp only [Complex.ofReal_intCast, Complex.ofReal_sub] at h1
    simp only [h1]
    ring
  · intro i j
    simp only [hz]
    ring
end GlobalTheory
