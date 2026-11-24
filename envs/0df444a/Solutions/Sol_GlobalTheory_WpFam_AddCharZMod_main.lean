-- Prove2me | solution 1 for GlobalTheory.WpFam.AddCharZMod.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:07.986129+00:00
-- url     : https://prove2.me/submissions/964a63a2-3151-414b-885a-8f23b2cbd9f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootOfUnityExpZModAdditiveCharacterProperties
import Theorems.Thm_GlobalTheory_WpFam_AddCharZMod_ch_eq

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
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.AddCharZMod
namespace GlobalTheory.WpFam.AddCharZMod
theorem _root_.solution : ∀ (N : ℕ) [NeZero N], (∀ n : ℤ, ch N (n : ZMod N) = Complex.exp (2 * Real.pi * Complex.I * n / N)) ∧ (∀ i j, ch N (i + j) = ch N i * ch N j) ∧ ch N 0 = 1 ∧ (∀ j, ch N j = 1 ↔ j = 0) ∧ (∀ (m : ℕ) j, ch N ((m : ZMod N) * j) = ch N j ^ m) ∧ (∀ j, ch N (-j) = (ch N j)⁻¹) ∧ (∀ j, ‖ch N j‖ = 1) ∧ (∀ j, IsIntegral ℤ (ch N j)) := by
  intro N _
  have hpow : ∀ (m : ℕ) (j : ZMod N), ch N ((m : ZMod N) * j) = ch N j ^ m := by
    intro m j
    rw [ch_eq, ch_eq, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hadd : ∀ i j, ch N (i + j) = ch N i * ch N j := by
    intro i j
    rw [ch_eq, ch_eq, ch_eq]
    exact AddChar.map_add_eq_mul _ i j
  have hzero : ch N 0 = 1 := by
    rw [ch_eq]
    exact AddChar.map_zero_eq_one _
  refine ⟨fun n => ?_, hadd, hzero, fun j => ?_, hpow, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [ch_eq]
    exact ZMod.stdAddChar_coe n
  · rw [ch_eq, ← (ZMod.stdAddChar (N := N)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff]
  · have h : ch N (-j) * ch N j = 1 := by
      rw [← hadd, neg_add_cancel, hzero]
    exact eq_inv_of_mul_eq_one_left h
  · rw [ch_eq, ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  · have h : ch N j ^ N = 1 := by
      rw [← hpow, ZMod.natCast_self, zero_mul, hzero]
    refine IsIntegral.of_pow (Nat.pos_of_neZero N) ?_
    rw [h]
    exact isIntegral_one
end GlobalTheory.WpFam.AddCharZMod
