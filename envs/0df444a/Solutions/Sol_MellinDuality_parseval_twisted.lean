-- Prove2me | solution 1 for MellinDuality.parseval_twisted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:30.707385+00:00
-- url     : https://prove2.me/submissions/2ada6589-326e-4354-b3bf-ce04d43b61d9

module
public import Definitions.Def_MellinDuality_Pairs
public import Definitions.Def_MellinDuality_MeanSquare
public import Theorems.Thm_MellinDuality_natCast_add_ne_zero_of_mem
public import Theorems.Thm_MellinDuality_natCast_ne_zero_of_mem


set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (w : ℕ → ℤ) :
    ∑ ψ : DirichletCharacter ℂ p,
        ψ (-1) * (((‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 : ℝ)) : ℂ) = 0 := by
  set I := Icc 1 ((p - 1) / 2)
  have hconj : ∀ ψ : DirichletCharacter ℂ p,
      ψ (-1) * (((‖∑ n ∈ I, ψ n * (w n : ℂ)‖ ^ 2 : ℝ)) : ℂ) =
        ∑ n ∈ I, ∑ n' ∈ I, (w n * w n' : ℂ) * (ψ n'⁻¹ * ψ (-(n : ZMod p))) := by
    intro ψ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun n' _ => ?_
    rw [map_mul, map_intCast]
    have : (starRingEnd ℂ) (ψ n') = ψ n'⁻¹ := by
      rw [← MulChar.inv_apply', ← MulChar.star_apply']; rfl
    rw [this, show -(n : ZMod p) = -1 * n by ring, map_mul]; ring
  simp_rw [hconj]
  rw [sum_comm]
  refine sum_eq_zero fun n hn => ?_
  rw [sum_comm]
  refine sum_eq_zero fun n' hn' => ?_
  rw [← mul_sum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ
    (isUnit_iff_ne_zero.2 (natCast_ne_zero_of_mem hn')) (-(n : ZMod p)),
    if_neg (natCast_add_ne_zero_of_mem hn hn'), mul_zero]
end MellinDuality
