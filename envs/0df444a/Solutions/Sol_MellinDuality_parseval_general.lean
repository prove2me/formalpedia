-- Prove2me | solution 1 for MellinDuality.parseval_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:29.122806+00:00
-- url     : https://prove2.me/submissions/ad18251f-4a15-4b38-a31f-b6a7187d25d2

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Parseval
public import Theorems.Thm_MellinDuality_natCast_ne_zero_of_mem
public import Theorems.Thm_MellinDuality_natCast_inj_of_mem
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
public import Theorems.Thm_MellinDuality_totient_cast
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (w : ℕ → ℤ) (hw : ∀ n, w n * w n = 1) :
    ∑ ψ : DirichletCharacter ℂ p,
        ‖∑ n ∈ Icc 1 ((p - 1) / 2), ψ n * (w n : ℂ)‖ ^ 2 =
      ((p : ℝ) - 1) * ((p - 1) / 2 : ℕ) := by
  set I := Icc 1 ((p - 1) / 2)
  have hconj : ∀ ψ : DirichletCharacter ℂ p,
      (((‖∑ n ∈ I, ψ n * (w n : ℂ)‖ ^ 2 : ℝ)) : ℂ) =
        ∑ n ∈ I, ∑ n' ∈ I, (w n * w n' : ℂ) * (ψ n'⁻¹ * ψ n) := by
    intro ψ
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]
    refine sum_congr rfl fun n _ => sum_congr rfl fun n' _ => ?_
    rw [map_mul, map_intCast]
    have : (starRingEnd ℂ) (ψ n') = ψ n'⁻¹ := by
      rw [← MulChar.inv_apply', ← MulChar.star_apply']; rfl
    rw [this]; ring
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [hconj]
  rw [sum_comm]
  have horth : ∀ n ∈ I, ∀ n' ∈ I, ∑ ψ : DirichletCharacter ℂ p, ψ (n' : ZMod p)⁻¹ * ψ n =
      if n' = n then (p : ℂ) - 1 else 0 := by
    intro n hn n' hn'
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ
      (isUnit_iff_ne_zero.2 (natCast_ne_zero_of_mem hn')) (n : ZMod p), totient_cast]
    simp only [natCast_inj_of_mem hn' hn]
  calc ∑ n ∈ I, ∑ ψ : DirichletCharacter ℂ p, ∑ n' ∈ I, (w n * w n' : ℂ) * (ψ n'⁻¹ * ψ n)
      = ∑ n ∈ I, ∑ n' ∈ I, (w n * w n' : ℂ) * (if n' = n then (p : ℂ) - 1 else 0) := by
        refine sum_congr rfl fun n hn => ?_
        rw [sum_comm]
        refine sum_congr rfl fun n' hn' => ?_
        rw [← mul_sum, horth n hn n' hn']
    _ = ∑ n ∈ I, ((p : ℂ) - 1) := by
        refine sum_congr rfl fun n hn => ?_
        simp only [mul_ite, mul_zero, sum_ite_eq', hn, ite_true]
        have := hw n
        have h' : (w n * w n : ℂ) = 1 := by exact_mod_cast this
        rw [h', one_mul]
    _ = (((((p : ℝ) - 1) * ((p - 1) / 2 : ℕ)) : ℝ) : ℂ) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
end MellinDuality
