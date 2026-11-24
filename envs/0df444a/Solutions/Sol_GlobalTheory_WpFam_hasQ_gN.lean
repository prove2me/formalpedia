-- Prove2me | solution 1 for GlobalTheory.WpFam.hasQ_gN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:13.759923+00:00
-- url     : https://prove2.me/submissions/a107e177-a6cf-4087-bc7b-6419105242dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassConstantQExpansion
import Theorems.Thm_GlobalTheory_WpFam_weierstrass_constant_eq_E2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam
namespace GlobalTheory.WpFam
theorem _root_.solution : ∀ (N : ℕ) [NeZero N], HasQ N gN (cG N) := by
  intro N _ τ
  have hN : N ≠ 0 := NeZero.ne N
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hinj : Function.Injective (fun m : ℕ => N * m) := fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h
  rw [← hinj.hasSum_iff]
  · have h := (EisensteinSeries.hasSum_qExpansion_E2 (z := τ)).mul_left (-1 / 12 : ℂ)
    rw [weierstrass_constant_eq_E2]
    convert! h using 1
    funext m
    have he : Complex.exp (2 * Real.pi * Complex.I * ((N * m : ℕ) : ℂ) * τ / N) =
        Complex.exp (2 * Real.pi * Complex.I * τ) ^ m := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp
    simp only [Function.comp, he, smul_eq_mul]
    by_cases hm : m = 0
    · simp [hm, cG]
    · have h1 : N * m ≠ 0 := mul_ne_zero hN hm
      simp only [cG, if_neg h1, if_neg hm, if_pos (dvd_mul_right N m),
        Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hN)]
      ring
  · intro k hk
    have hd : ¬ N ∣ k := fun ⟨m, hm⟩ => hk ⟨m, hm.symm⟩
    have h0 : k ≠ 0 := fun h => hd (h ▸ dvd_zero N)
    simp [cG, hd, h0]
end GlobalTheory.WpFam
