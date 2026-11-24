-- Prove2me | solution 1 for GlobalTheory.ClassFin.unipotent_size_reduction_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:12:08.935383+00:00
-- url     : https://prove2.me/submissions/66fb7729-7b6a-44e7-8a79-3e118a11daaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnipotentUpperSizeReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution {N : ℕ} (n : Matrix (Fin N) (Fin N) ℝ)
    (h1 : ∀ i, n i i = 1) (h0 : ∀ i j, j < i → n i j = 0) (j : Fin N) (k : ℕ) :
    ∃ z : Fin N → ℤ, z j = 1 ∧ (∀ l, j < l → z l = 0) ∧
      ∀ i, i < j → (j : ℕ) ≤ i + k → |∑ l, n i l * (z l : ℝ)| ≤ 1 / 2 := by
  induction k with
  | zero =>
    refine ⟨Pi.single j 1, by simp, fun l hl => by simp [Pi.single_apply, hl.ne'], ?_⟩
    intro i hi hk
    exact absurd hk (by have : (i : ℕ) < j := hi; omega)
  | succ k ih =>
    obtain ⟨z, hz1, hz0, hz⟩ := ih
    by_cases hk : k + 1 ≤ (j : ℕ)
    · let i0 : Fin N := ⟨j - (k + 1), by have := j.2; omega⟩
      have hi0v : (i0 : ℕ) = j - (k + 1) := rfl
      have hi0 : i0 < j := by
        show (i0 : ℕ) < j
        omega
      set c : ℤ := -round (∑ l, n i0 l * (z l : ℝ)) with hc
      have key : ∀ i, ∑ l, n i l * (((z + Pi.single i0 c : Fin N → ℤ) l : ℤ) : ℝ)
          = ∑ l, n i l * (z l : ℝ) + n i i0 * c := by
        intro i
        simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single i0]
        · simp
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · simp
      refine ⟨z + Pi.single i0 c, ?_, ?_, ?_⟩
      · simp [Pi.single_apply, hi0.ne', hz1]
      · intro l hl
        simp [Pi.single_apply, (hi0.trans hl).ne', hz0 l hl]
      · intro i hi hik
        rw [key]
        by_cases h : i = i0
        · subst h
          rw [h1, one_mul, hc, Int.cast_neg, ← sub_eq_add_neg]
          exact abs_sub_round _
        · have hne : (i : ℕ) ≠ i0 := fun e => h (Fin.ext e)
          have hlt : i0 < i := by
            show (i0 : ℕ) < i
            omega
          rw [h0 i i0 hlt, zero_mul, add_zero]
          exact hz i hi (by omega)
    · exact ⟨z, hz1, hz0, fun i hi _ => hz i hi (by omega)⟩
end GlobalTheory.ClassFin
