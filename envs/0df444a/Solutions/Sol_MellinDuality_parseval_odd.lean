-- Prove2me | solution 1 for MellinDuality.parseval_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:39.13342+00:00
-- url     : https://prove2.me/submissions/8807c0f5-4be6-4323-8640-5a7cbd9be2d0

module
public import Definitions.Def_MellinDuality_Pairs
public import Definitions.Def_MellinDuality_MeanSquare
public import Theorems.Thm_MellinDuality_char_neg_one_sq
public import Theorems.Thm_MellinDuality_parseval_twisted
public import Theorems.Thm_MellinDuality_parseval_general


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (w : ℕ → ℤ) (hw : ∀ n, w n * w n = 1) :
    ∑ ψ ∈ oddChars p, ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) / 2 * ((p - 1) / 2 : ℕ) := by
  have hall := parseval_general (p := p) w hw
  have htw := parseval_twisted (p := p) w
  have hsplit : ∀ (ψ : DirichletCharacter ℂ p) (x : ℝ),
      ((if ψ (-1) = -1 then x else 0 : ℝ) : ℂ) = ((x : ℂ) - ψ (-1) * (x : ℂ)) / 2 := by
    intro ψ x
    rcases mul_self_eq_one_iff.1 (char_neg_one_sq ψ) with h | h
    · rw [if_neg (by rw [h]; norm_num), h]; push_cast; ring
    · rw [if_pos h, h]; ring
  apply Complex.ofReal_injective
  rw [oddChars, sum_filter, Complex.ofReal_sum]
  simp_rw [hsplit]
  rw [← sum_div, sum_sub_distrib, htw, sub_zero, ← Complex.ofReal_sum, hall]
  push_cast; ring
end MellinDuality
